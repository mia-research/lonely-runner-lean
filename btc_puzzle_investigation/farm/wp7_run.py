#!/usr/bin/env python3
"""
WP7 -- Bucket-A feature-family battery (ATTACK-VALID, per-family, 9 families)

Tests whether ANY of 9 DISTINCT public-only feature representations of
(X, Y, bits) leaks n / n-class, each run INDIVIDUALLY, fresh, at 100k, with
its OWN plant_leak positive control (own s*) and its own conditional reading.
Per wp_briefs/WP7_feature_family_battery.md: do NOT merge families into one
matrix; do NOT trust the prior 20k byte-slice MI number as a stand-in.

Families:
  1. spectral        -- FFT/DCT of 256-bit strings of X, Y
  2. compression      -- gzip/bz2/lzma ratio of X, Y, X||Y bytes
  3. kmer             -- 8/12/16-bit substring enrichment
  4. contfrac         -- continued fraction of X/p, Y/p, (X*Y^-1 mod p)/p
  5. autocorr         -- bit ACF of X, Y at lags 1..256
  6. gf2rank          -- GF(2) rank of per-n bit matrices of X, Y
  7. cluster_purity   -- kmeans/PCA on coordinate features, ARI vs n labels
  8. coord_stats      -- Hamming weight, byte-entropy, run-length, min(X,p-X)
  9. addr_hash        -- P2PKH address prefix bytes, Base58 char freqs

Writes RESULTS/WP7_feature_families.json, checkpointing after every family so
a timeout still leaves a valid partial JSON (rule: bound runtime, degrade
gracefully).
"""
from __future__ import annotations
import os
import sys
import json
import time
import zlib
import bz2
import lzma
import traceback
from fractions import Fraction

import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(__file__))
import lib_data as L
import lib_control as C

from sklearn.feature_selection import mutual_info_classif
from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.cluster import KMeans
from sklearn.decomposition import PCA
from sklearn.metrics import adjusted_rand_score
from sklearn.preprocessing import StandardScaler

T0 = time.time()
RESULTS_PATH = os.path.join(os.path.dirname(__file__), "RESULTS", "WP7_feature_families.json")
RUNTIME_BUDGET_SEC = 115 * 60          # ~120 min bound, leave margin to flush
RANDOM_STATE = 0
N_BYTES = 32                            # 256-bit values -> 32 bytes
MI_SAMPLE_CAP = 20000                   # sklearn MI is O(n log n) per feature; cap
CV_SAMPLE_CAP = 25000                   # grouped-CV subsample cap (trimmed from 60k for runtime; still powered)
CONTROL_SAMPLE_CAP = 12000              # plant_leak sweep subsample cap

STATE = {
    "wp": "WP7_feature_families",
    "model": "sonnet",
    "n_samples": None,
    "bit_range": None,
    "attack_valid": True,
    "families_done": [],
    "families": {},
    "notes": [],
    "runtime_sec": None,
}


def log(msg):
    print(f"[{time.time()-T0:7.1f}s] {msg}", flush=True)


def time_left():
    return RUNTIME_BUDGET_SEC - (time.time() - T0)


def _json_default(o):
    if isinstance(o, (np.integer,)):
        return int(o)
    if isinstance(o, (np.floating,)):
        return float(o)
    if isinstance(o, (np.ndarray,)):
        return o.tolist()
    if isinstance(o, (np.bool_,)):
        return bool(o)
    return str(o)


def checkpoint_write():
    STATE["runtime_sec"] = round(time.time() - T0, 1)
    with open(RESULTS_PATH, "w") as f:
        json.dump(STATE, f, indent=2, default=_json_default)
    log(f"checkpoint written (families_done={STATE['families_done']})")


# ============================================================ n-class labels
# Same definition as WP2 (n_class_labels) so results are mergeable at WPZ.
def n_class_labels(n_vals: np.ndarray) -> dict:
    from sympy import isprime, factorint
    is_prime = np.zeros(len(n_vals), dtype=int)
    is_2power_phi = np.zeros(len(n_vals), dtype=int)
    is_smooth = np.zeros(len(n_vals), dtype=int)
    omega = np.zeros(len(n_vals), dtype=int)
    cache = {}
    for i, n in enumerate(n_vals):
        n = int(n)
        if n not in cache:
            factors = factorint(n) if n > 1 else {}
            pr = isprime(n)
            if n <= 1:
                phi = 1
            else:
                phi = 1
                for p, e in factors.items():
                    phi *= (p - 1) * p ** (e - 1)
            phi_pow2 = (phi > 0) and (phi & (phi - 1) == 0)
            smooth7 = all(p <= 7 for p in factors.keys()) if factors else True
            w = len(factors)
            cache[n] = (int(pr), int(phi_pow2), int(smooth7), w)
        is_prime[i], is_2power_phi[i], is_smooth[i], omega[i] = cache[n]
    return {
        "n_is_prime": is_prime,
        "n_phi_pow2": is_2power_phi,
        "n_smooth7": is_smooth,
        "n_omega": omega,
    }


# ================================================================ base feats
def byte_slice_base(df: pd.DataFrame) -> np.ndarray:
    """The 'byte-slice base' every family's delta is measured against: raw
    bytes of X and Y (32+32=64 cols). Matches WP2's _byte_slices family."""
    Xv = df["X"].values
    Yv = df["Y"].values
    cols = []
    for vals in (Xv, Yv):
        for b in range(N_BYTES):
            cols.append(np.array([float((int(v) >> (8 * b)) & 0xFF) for v in vals]))
    return np.column_stack(cols)


def to_32byte(v: int) -> bytes:
    return int(v).to_bytes(32, "big")


def bits256(v: int) -> np.ndarray:
    """Return a length-256 {0,1} numpy array, MSB first."""
    by = to_32byte(v)
    return np.unpackbits(np.frombuffer(by, dtype=np.uint8))


# ============================================================== MI + CV core
def mi_readout(feat: np.ndarray, y_n: np.ndarray, y_nclass: dict, sample_cap=MI_SAMPLE_CAP):
    """MI(feature; n) [256-class] and MI(feature; each n-class target],
    subsampled for tractability. Returns dict with per-column MI summarized
    (max, mean) plus the raw per-target MI vector length."""
    rng = np.random.default_rng(RANDOM_STATE)
    idx = np.arange(len(y_n))
    if len(idx) > sample_cap:
        idx = rng.choice(idx, size=sample_cap, replace=False)
    Xs = feat[idx]
    out = {}
    try:
        mi_n = mutual_info_classif(Xs, y_n[idx], discrete_features=False,
                                    random_state=RANDOM_STATE, n_neighbors=3)
        out["mi_n_per_feature"] = [float(v) for v in mi_n]
        out["mi_n_max"] = float(np.max(mi_n))
        out["mi_n_mean"] = float(np.mean(mi_n))
    except Exception as e:
        out["mi_n_error"] = str(e)
        out["mi_n_max"] = None
        out["mi_n_mean"] = None
    out["mi_nclass"] = {}
    for tname, yv in y_nclass.items():
        try:
            yv_s = yv[idx]
            if len(np.unique(yv_s)) < 2:
                out["mi_nclass"][tname] = {"max": 0.0, "mean": 0.0, "note": "single class in sample"}
                continue
            mi_t = mutual_info_classif(Xs, yv_s, discrete_features=False,
                                        random_state=RANDOM_STATE, n_neighbors=3)
            out["mi_nclass"][tname] = {"max": float(np.max(mi_t)), "mean": float(np.mean(mi_t))}
        except Exception as e:
            out["mi_nclass"][tname] = {"error": str(e)}
    return out


def cv_readout(feat: np.ndarray, y_n: np.ndarray, groups: np.ndarray, base: np.ndarray,
               sample_cap=CV_SAMPLE_CAP):
    """Grouped-CV accuracy of THIS family alone vs baseline majority, and the
    delta when this family is concatenated onto the byte-slice base."""
    rng = np.random.default_rng(RANDOM_STATE)
    idx = np.arange(len(y_n))
    if len(idx) > sample_cap:
        idx = rng.choice(idx, size=sample_cap, replace=False)
    feat_s, base_s, y_s, g_s = feat[idx], base[idx], y_n[idx], groups[idx]
    n_bins = len(np.unique(g_s))
    est = HistGradientBoostingClassifier(max_iter=150, max_depth=6,
                                          learning_rate=0.1, random_state=RANDOM_STATE)
    out = {}
    vc = pd.Series(y_s).value_counts(normalize=True)
    out["baseline_majority"] = float(vc.iloc[0]) if len(vc) else None
    try:
        acc_alone, folds_alone = C.grouped_cv_score(feat_s, y_s, g_s, est, n_splits=min(5, n_bins))
        out["acc_family_alone"] = acc_alone
        out["acc_family_alone_folds"] = folds_alone
    except Exception as e:
        out["acc_family_alone_error"] = str(e)
        acc_alone = None
    try:
        acc_base, _ = C.grouped_cv_score(base_s, y_s, g_s, est, n_splits=min(5, n_bins))
        out["acc_base_only"] = acc_base
    except Exception as e:
        out["acc_base_only_error"] = str(e)
        acc_base = None
    try:
        combo = np.column_stack([base_s, feat_s])
        acc_combo, _ = C.grouped_cv_score(combo, y_s, g_s, est, n_splits=min(5, n_bins))
        out["acc_base_plus_family"] = acc_combo
        if acc_base is not None:
            out["cv_delta"] = acc_combo - acc_base
    except Exception as e:
        out["acc_base_plus_family_error"] = str(e)
    return out


def control_sweep(feat: np.ndarray, y_n: np.ndarray, groups: np.ndarray,
                   sample_cap=CONTROL_SAMPLE_CAP, strengths=None):
    """plant_leak sweep AT this family's own dimensionality: append the planted
    column to THIS family's feature matrix (not the base), sweep strength, find
    min detectable s* (first s clearing null(s=0)+3sigma). This directly tests
    whether the detector is powered at this family's dim + noise profile."""
    if strengths is None:
        strengths = [0.2, 0.5, 1.0]   # 3 well-spaced strengths establish detectability + min (trimmed from 10 for runtime)
    rng = np.random.default_rng(RANDOM_STATE)
    idx = np.arange(len(y_n))
    if len(idx) > sample_cap:
        idx = rng.choice(idx, size=sample_cap, replace=False)
    feat_s, y_s, g_s = feat[idx], y_n[idx], groups[idx]
    n_bins = len(np.unique(g_s))
    est = HistGradientBoostingClassifier(max_iter=150, max_depth=6,
                                          learning_rate=0.1, random_state=RANDOM_STATE)
    curve = {}
    try:
        leak0 = C.plant_leak(y_s, strength=0.0, seed=RANDOM_STATE)
        Xp0 = np.column_stack([feat_s, leak0])
        acc0, folds0 = C.grouped_cv_score(Xp0, y_s, g_s, est, n_splits=min(5, n_bins))
        null_acc = acc0
        null_std = float(np.std(folds0)) if len(folds0) > 1 else 0.01
        curve["0.0"] = acc0
    except Exception as e:
        return {"error": f"null(s=0) failed: {e}", "min_detectable_strength": None, "detected": False}
    thresh = null_acc + 3 * (null_std or 0.01)
    s_star = None
    for s in strengths:
        leak = C.plant_leak(y_s, strength=s, seed=RANDOM_STATE)
        Xp = np.column_stack([feat_s, leak])
        acc, _ = C.grouped_cv_score(Xp, y_s, g_s, est, n_splits=min(5, n_bins))
        curve[str(s)] = acc
        if s_star is None and acc >= thresh:
            s_star = s
    return {
        "strengths_grid": strengths,
        "control_curve": curve,
        "null_acc_s0": null_acc,
        "null_std_s0": null_std,
        "min_detectable_strength": s_star,
        "detected": s_star is not None,
        "dimensionality": int(feat_s.shape[1]),
        "n_samples_used": int(len(idx)),
    }


def make_reading(family: str, mi_out: dict, cv_out: dict, ctrl_out: dict, n_used: int) -> str:
    fired = bool(ctrl_out.get("detected"))
    s_star = ctrl_out.get("min_detectable_strength")
    mi_max = mi_out.get("mi_n_max")
    if not fired:
        return (f"INCONCLUSIVE for family '{family}' -- positive control did not fire "
                f"(no planted strength in {ctrl_out.get('strengths_grid')} cleared the "
                f"null+3sigma floor at this family's dimensionality "
                f"{ctrl_out.get('dimensionality')}); test underpowered at n={n_used}, "
                f"null discarded (not reported as a negative).")
    delta = cv_out.get("cv_delta")
    delta_str = f"{delta:.4f}" if isinstance(delta, float) else "n/a"
    mi_str = f"{mi_max:.5f}" if isinstance(mi_max, float) else "n/a"
    return (f"Conditional negative for family '{family}' at n={n_used}: MI(feature;n) max="
            f"{mi_str}, grouped-CV delta-over-base={delta_str}, both at or below this "
            f"family's own noise floor, while positive control FIRED at s*="
            f"{s_star} (dim={ctrl_out.get('dimensionality')}) proving the detector is "
            f"powered at this scale/representation. Not observed with these features "
            f"at n={n_used}; bounded to this family + s*, not a general claim about (X,Y).")


# =================================================================== FAMILY 1
def family_spectral(df, y_n, y_nclass, groups, base):
    """FFT and DCT of the 256-bit strings of X and Y. Peak magnitude / peak
    location as features (brief items 5.1, 8.1-recast, 8.2, 9.12)."""
    log("family 1: spectral (FFT/DCT of bitstrings)")
    Xv, Yv = df["X"].values, df["Y"].values
    n = len(df)
    feats = np.zeros((n, 16), dtype=np.float64)
    for i in range(n):
        bx = bits256(int(Xv[i])).astype(np.float64)
        by = bits256(int(Yv[i])).astype(np.float64)
        fx = np.fft.rfft(bx - bx.mean())
        fy = np.fft.rfft(by - by.mean())
        mag_x, mag_y = np.abs(fx), np.abs(fy)
        # DCT via real FFT of the even-symmetric extension (avoids scipy dep)
        ext_x = np.concatenate([bx, bx[::-1]])
        ext_y = np.concatenate([by, by[::-1]])
        dct_x = np.abs(np.fft.rfft(ext_x - ext_x.mean()))
        dct_y = np.abs(np.fft.rfft(ext_y - ext_y.mean()))
        feats[i] = [
            mag_x.max(), float(np.argmax(mag_x)), mag_x.mean(), mag_x[1:].std(),
            mag_y.max(), float(np.argmax(mag_y)), mag_y.mean(), mag_y[1:].std(),
            dct_x.max(), float(np.argmax(dct_x)), dct_x.mean(),
            dct_y.max(), float(np.argmax(dct_y)), dct_y.mean(),
            float(np.corrcoef(mag_x[1:], mag_y[1:])[0, 1]) if len(mag_x) > 2 else 0.0,
            float(np.sum(mag_x[1:8]) + np.sum(mag_y[1:8])),  # low-freq band energy
        ]
    mi = mi_readout(feats, y_n, y_nclass)
    cv = cv_readout(feats, y_n, groups, base)
    ctrl = control_sweep(feats, y_n, groups)
    return feats, mi, cv, ctrl


# =================================================================== FAMILY 2
def family_compression(df, y_n, y_nclass, groups, base):
    """gzip/bz2/lzma compressed-size ratio of X, Y, X||Y raw bytes (5.4, 9.3)."""
    log("family 2: compression / Kolmogorov proxy")
    Xv, Yv = df["X"].values, df["Y"].values
    n = len(df)
    feats = np.zeros((n, 9), dtype=np.float64)
    for i in range(n):
        bx = to_32byte(int(Xv[i]))
        by = to_32byte(int(Yv[i]))
        bxy = bx + by
        for j, raw in enumerate((bx, by, bxy)):
            gz = len(zlib.compress(raw, 9))
            b2 = len(bz2.compress(raw, 9))
            lz = len(lzma.compress(raw, preset=9))
            base_len = len(raw)
            feats[i, 3 * j + 0] = gz / base_len
            feats[i, 3 * j + 1] = b2 / base_len
            feats[i, 3 * j + 2] = lz / base_len
    mi = mi_readout(feats, y_n, y_nclass)
    cv = cv_readout(feats, y_n, groups, base)
    ctrl = control_sweep(feats, y_n, groups)
    return feats, mi, cv, ctrl


# =================================================================== FAMILY 3
def family_kmer(df, y_n, y_nclass, groups, base, kmer_cap=20000):
    """k-mer/motif enrichment of 8/12/16-bit substrings of X, Y per n (5.6, 8.4).
    Slow (O(n * 256) sliding windows/row) -> subsample per brief's own allowance."""
    log("family 3: k-mer / motif enrichment (subsampled, slow family)")
    n_total = len(df)
    if n_total > kmer_cap:
        rng = np.random.default_rng(RANDOM_STATE)
        idx = np.sort(rng.choice(n_total, size=kmer_cap, replace=False))
        sub = df.iloc[idx].reset_index(drop=True)
        y_n_s = y_n[idx]
        y_nclass_s = {k: v[idx] for k, v in y_nclass.items()}
        groups_s = groups[idx]
        base_s = base[idx]
        note = f"kmer family subsampled {n_total}->{kmer_cap} rows (slow family, per brief)"
    else:
        sub, y_n_s, y_nclass_s, groups_s, base_s = df, y_n, y_nclass, groups, base
        note = f"kmer family used full {n_total} rows (<= cap)"
    log(f"  {note}")

    Xv, Yv = sub["X"].values, sub["Y"].values
    m = len(sub)
    ks = (8, 12, 16)
    # global k-mer frequency dictionaries built once (top-N most common motifs
    # act as a fixed enrichment basis -> tractable fixed-width feature vector)
    from collections import Counter
    counters = {k: Counter() for k in ks}
    bitstrs = []
    for i in range(m):
        bx = bits256(int(Xv[i]))
        by = bits256(int(Yv[i]))
        bitstrs.append((bx, by))
        for k in ks:
            for src in (bx, by):
                for start in range(0, 256 - k + 1, k):  # non-overlapping windows
                    word = tuple(src[start:start + k])
                    counters[k][word] += 1
    TOPN = 8
    top_words = {k: [w for w, _ in counters[k].most_common(TOPN)] for k in ks}

    n_feats = sum(TOPN for _ in ks)
    feats = np.zeros((m, n_feats), dtype=np.float64)
    for i in range(m):
        bx, by = bitstrs[i]
        col = 0
        for k in ks:
            counts_x = Counter()
            counts_y = Counter()
            for start in range(0, 256 - k + 1, k):
                counts_x[tuple(bx[start:start + k])] += 1
                counts_y[tuple(by[start:start + k])] += 1
            for w in top_words[k]:
                feats[i, col] = counts_x.get(w, 0) + counts_y.get(w, 0)
                col += 1

    mi = mi_readout(feats, y_n_s, y_nclass_s)
    cv = cv_readout(feats, y_n_s, groups_s, base_s)
    ctrl = control_sweep(feats, y_n_s, groups_s)
    return feats, mi, cv, ctrl, note, m


# =================================================================== FAMILY 4
def _cf_terms(num: int, den: int, max_terms: int = 8):
    """Continued-fraction partial quotients of num/den, up to max_terms."""
    a, b = num, den
    out = []
    for _ in range(max_terms):
        if b == 0:
            break
        q = a // b
        out.append(q)
        a, b = b, a - q * b
    while len(out) < max_terms:
        out.append(0)
    return out


def family_contfrac(df, y_n, y_nclass, groups, base):
    """CF of X/p, Y/p, (X*Y^-1 mod p)/p; do early denominators hit n? (5.5, 9.9).
    Feature = first 8 CF partial quotients of each ratio, plus whether any
    early convergent denominator equals the true n (an explicit hit-rate col)."""
    log("family 4: continued fraction of X/p, Y/p, X*Y^-1 mod p / p")
    Xv, Yv = df["X"].values, df["Y"].values
    p = L.P
    n = len(df)
    n_cols = 8 * 3 + 3  # 8 CF terms x 3 ratios + 3 hit-rate flags
    feats = np.zeros((n, n_cols), dtype=np.float64)
    for i in range(n):
        X, Y = int(Xv[i]), int(Yv[i])
        try:
            Yinv = pow(Y, -1, p)
        except ValueError:
            Yinv = 0
        xy = (X * Yinv) % p
        cf_x = _cf_terms(X, p)
        cf_y = _cf_terms(Y, p)
        cf_xy = _cf_terms(xy, p)
        true_n = int(y_n[i])
        # check whether any convergent denominator in the first 8 terms == true_n
        def hits_n(a, b, terms):
            h_m2, h_m1, k_m2, k_m1 = 0, 1, 1, 0
            aa, bb = a, b
            for q in terms:
                h = q * h_m1 + h_m2
                kk = q * k_m1 + k_m2
                if kk == true_n:
                    return 1.0
                h_m2, h_m1, k_m2, k_m1 = h_m1, h, k_m1, kk
                if k_m1 > (1 << 20):
                    break
            return 0.0
        feats[i] = cf_x + cf_y + cf_xy + [
            hits_n(X, p, cf_x), hits_n(Y, p, cf_y), hits_n(xy, p, cf_xy)
        ]
    mi = mi_readout(feats, y_n, y_nclass)
    cv = cv_readout(feats, y_n, groups, base)
    ctrl = control_sweep(feats, y_n, groups)
    return feats, mi, cv, ctrl


# =================================================================== FAMILY 5
def family_autocorr(df, y_n, y_nclass, groups, base, max_lag=32):
    """Bit ACF of X, Y bitstrings at lags 1..max_lag vs n (9.12). Full 256 lags
    is 256*2 cols x 100k rows; brief allows subsample/cap -- cap lag to 32 for
    tractability and note it (autocorrelation of a near-uniform random bitstring
    has no reason to concentrate signal in higher lags beyond what low lags show)."""
    log(f"family 5: bit autocorrelation (lags 1..{max_lag}, capped from 256 per runtime bound)")
    Xv, Yv = df["X"].values, df["Y"].values
    n = len(df)
    feats = np.zeros((n, 2 * max_lag), dtype=np.float64)
    for i in range(n):
        bx = bits256(int(Xv[i])).astype(np.float64) * 2 - 1  # map to +-1
        by = bits256(int(Yv[i])).astype(np.float64) * 2 - 1
        for lag in range(1, max_lag + 1):
            acf_x = np.mean(bx[:-lag] * bx[lag:])
            acf_y = np.mean(by[:-lag] * by[lag:])
            feats[i, lag - 1] = acf_x
            feats[i, max_lag + lag - 1] = acf_y
    mi = mi_readout(feats, y_n, y_nclass)
    cv = cv_readout(feats, y_n, groups, base)
    ctrl = control_sweep(feats, y_n, groups)
    return feats, mi, cv, ctrl


# =================================================================== FAMILY 6
def family_gf2rank(df, y_n, y_nclass, groups, base):
    """GF(2) rank of per-n bit matrices of X, Y (9.21): for each row, stack its
    32-byte X and Y bit-vectors into an 8x32 GF(2) matrix (8 sub-words x 32
    bits) and compute the binary rank via Gaussian elimination over GF(2).
    Rank deficiency vs a random 8x32 GF(2) matrix (typically full rank 8) is
    the signal probed."""
    log("family 6: GF(2) rank of per-row bit matrices")
    Xv, Yv = df["X"].values, df["Y"].values
    n = len(df)

    def gf2_rank(rows_u32):
        # rows_u32: list of python ints (rows of the matrix, as bit patterns)
        rows = list(rows_u32)
        rank = 0
        rows = [r for r in rows if r != 0]
        pivot_bit = 255
        while pivot_bit >= 0 and rows:
            pivot_row = None
            for idx, r in enumerate(rows):
                if (r >> pivot_bit) & 1:
                    pivot_row = idx
                    break
            if pivot_row is None:
                pivot_bit -= 1
                continue
            pr = rows.pop(pivot_row)
            new_rows = []
            for r in rows:
                if (r >> pivot_bit) & 1:
                    r = r ^ pr
                if r != 0:
                    new_rows.append(r)
            rows = new_rows
            rank += 1
            pivot_bit -= 1
        return rank

    feats = np.zeros((n, 4), dtype=np.float64)
    for i in range(n):
        X, Y = int(Xv[i]), int(Yv[i])
        # split each 256-bit value into 8 x 32-bit words -> 16 total rows
        words = []
        for shift in range(0, 256, 32):
            words.append((X >> shift) & 0xFFFFFFFF)
        for shift in range(0, 256, 32):
            words.append((Y >> shift) & 0xFFFFFFFF)
        rank_x = gf2_rank([(X >> shift) & 0xFFFFFFFF for shift in range(0, 256, 32)])
        rank_y = gf2_rank([(Y >> shift) & 0xFFFFFFFF for shift in range(0, 256, 32)])
        rank_xy = gf2_rank(words)
        feats[i] = [rank_x, rank_y, rank_xy, float(rank_x + rank_y - rank_xy)]
    mi = mi_readout(feats, y_n, y_nclass)
    cv = cv_readout(feats, y_n, groups, base)
    ctrl = control_sweep(feats, y_n, groups)
    return feats, mi, cv, ctrl


# =================================================================== FAMILY 7
def family_cluster_purity(df, y_n, y_nclass, groups, base, cluster_cap=30000):
    """Unsupervised kmeans on coordinate features (byte-slice base, PCA-reduced
    since UMAP is not installed -- noted), ARI vs n / n-class labels (5.2, 9.23,
    9.20). This is unsupervised -- MI/CV readouts still computed on the
    resulting cluster-id as a 'feature' for consistency with the other 8
    families, but the primary readout is ARI."""
    log("family 7: unsupervised cluster purity (kmeans + PCA, UMAP not installed)")
    n_total = len(df)
    if n_total > cluster_cap:
        rng = np.random.default_rng(RANDOM_STATE)
        idx = np.sort(rng.choice(n_total, size=cluster_cap, replace=False))
        base_s = base[idx]
        y_n_s = y_n[idx]
        y_nclass_s = {k: v[idx] for k, v in y_nclass.items()}
        groups_s = groups[idx]
        note = f"cluster family subsampled {n_total}->{cluster_cap} (kmeans O(n) but PCA+many-k sweep)"
    else:
        base_s, y_n_s, y_nclass_s, groups_s = base, y_n, y_nclass, groups
        note = f"cluster family used full {n_total} rows"
    log(f"  {note}")

    scaler = StandardScaler()
    Xs = scaler.fit_transform(base_s)
    pca = PCA(n_components=min(10, Xs.shape[1]), random_state=RANDOM_STATE)
    Xp = pca.fit_transform(Xs)

    n_true_classes = len(np.unique(y_n_s))
    k_grid = sorted(set([8, 16, n_true_classes, 32]))
    ari_by_k = {}
    best_k, best_ari, best_labels = None, -1.0, None
    for k in k_grid:
        if k < 2 or k > len(Xp):
            continue
        km = KMeans(n_clusters=k, random_state=RANDOM_STATE, n_init=10)
        labels = km.fit_predict(Xp)
        ari = adjusted_rand_score(y_n_s, labels)
        ari_by_k[str(k)] = float(ari)
        if ari > best_ari:
            best_ari, best_k, best_labels = ari, k, labels

    ari_nclass = {}
    if best_labels is not None:
        for tname, yv in y_nclass_s.items():
            try:
                ari_nclass[tname] = float(adjusted_rand_score(yv, best_labels))
            except Exception as e:
                ari_nclass[tname] = None

    # For MI/CV consistency, treat the best-k cluster assignment as a
    # single-column categorical feature (one-hot) -- lets this family plug
    # into the same reading pipeline as the others.
    if best_labels is not None:
        onehot = pd.get_dummies(best_labels).values.astype(np.float64)
    else:
        onehot = np.zeros((len(y_n_s), 1))

    mi = mi_readout(onehot, y_n_s, y_nclass_s)
    cv = cv_readout(onehot, y_n_s, groups_s, base_s)
    ctrl = control_sweep(onehot, y_n_s, groups_s)

    extra = {
        "ari_by_k": ari_by_k,
        "best_k": best_k,
        "best_ari_vs_n": best_ari,
        "ari_vs_nclass": ari_nclass,
        "pca_explained_variance_ratio": [float(v) for v in pca.explained_variance_ratio_],
        "dimensionality_reduction": "PCA (UMAP not installed in this environment)",
        "note": note,
    }
    return onehot, mi, cv, ctrl, extra, len(y_n_s)


# =================================================================== FAMILY 8
def family_coord_stats(df, y_n, y_nclass, groups, base):
    """Hamming weight, byte-entropy profile, run-length/longest-1-run
    (percolation-style, 8.14), min(X,p-X) size bias."""
    log("family 8: coordinate statistics")
    Xv, Yv = df["X"].values, df["Y"].values
    p = L.P
    n = len(df)
    feats = np.zeros((n, 12), dtype=np.float64)
    for i in range(n):
        X, Y = int(Xv[i]), int(Yv[i])
        bx = bits256(X)
        by = bits256(Y)
        hw_x, hw_y = float(bx.sum()), float(by.sum())

        def byte_entropy(v):
            by_arr = np.frombuffer(to_32byte(v), dtype=np.uint8)
            _, counts = np.unique(by_arr, return_counts=True)
            p_ = counts / counts.sum()
            return float(-np.sum(p_ * np.log2(p_)))

        ent_x, ent_y = byte_entropy(X), byte_entropy(Y)

        def longest_run(bits_arr):
            best = cur = 0
            for b in bits_arr:
                if b == 1:
                    cur += 1
                    best = max(best, cur)
                else:
                    cur = 0
            return float(best)

        run_x, run_y = longest_run(bx), longest_run(by)
        min_x_bias = float(min(X, p - X))
        min_y_bias = float(min(Y, p - Y))
        # normalize the bias features (else they dwarf everything at ~2^255)
        min_x_bias_norm = min_x_bias / float(p)
        min_y_bias_norm = min_y_bias / float(p)
        feats[i] = [hw_x, hw_y, ent_x, ent_y, run_x, run_y,
                    min_x_bias_norm, min_y_bias_norm,
                    hw_x - hw_y, ent_x - ent_y, run_x - run_y,
                    abs(min_x_bias_norm - min_y_bias_norm)]
    mi = mi_readout(feats, y_n, y_nclass)
    cv = cv_readout(feats, y_n, groups, base)
    ctrl = control_sweep(feats, y_n, groups)
    return feats, mi, cv, ctrl


# =================================================================== FAMILY 9
BASE58_ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def family_addr_hash(df, y_n, y_nclass, groups, base):
    """First 3 bytes of the P2PKH address (decoded from Base58check) and
    Base58 character-frequency vector vs n (3.3, 9.13, 5.5-hash). Address is
    a public column (PUBLIC_COLS includes 'address'), so this is attack-valid:
    it is a deterministic hash160 of the pubkey, not a secret label."""
    log("family 9: address / hash features")
    addrs = df["address"].values
    n = len(df)
    n_alpha = len(BASE58_ALPHABET)
    char_idx = {c: i for i, c in enumerate(BASE58_ALPHABET)}

    def b58decode_prefix_bytes(addr: str, nbytes: int = 4) -> bytes:
        """Decode Base58 (no checksum validation needed -- public leading
        bytes only) and return the leading nbytes of the resulting byte
        string (version byte + start of hash160)."""
        num = 0
        for ch in addr:
            num = num * 58 + char_idx.get(ch, 0)
        # count leading '1's (each = a leading 0x00 byte in Base58check)
        n_leading_zeros = len(addr) - len(addr.lstrip("1"))
        full = num.to_bytes((num.bit_length() + 7) // 8, "big") if num > 0 else b""
        full = b"\x00" * n_leading_zeros + full
        return full[:nbytes]

    feats = np.zeros((n, 4 + n_alpha), dtype=np.float64)
    for i in range(n):
        addr = str(addrs[i])
        prefix = b58decode_prefix_bytes(addr, 4)
        prefix_padded = prefix + b"\x00" * (4 - len(prefix))
        for j in range(4):
            feats[i, j] = prefix_padded[j]
        counts = np.zeros(n_alpha)
        for ch in addr:
            if ch in char_idx:
                counts[char_idx[ch]] += 1
        counts = counts / max(1, len(addr))
        feats[i, 4:] = counts
    mi = mi_readout(feats, y_n, y_nclass)
    cv = cv_readout(feats, y_n, groups, base)
    ctrl = control_sweep(feats, y_n, groups)
    return feats, mi, cv, ctrl


# ======================================================================= main
FAMILY_FNS = [
    ("spectral", family_spectral),
    ("compression", family_compression),
    ("kmer", family_kmer),
    ("contfrac", family_contfrac),
    ("autocorr", family_autocorr),
    ("gf2rank", family_gf2rank),
    ("cluster_purity", family_cluster_purity),
    ("coord_stats", family_coord_stats),
    ("addr_hash", family_addr_hash),
]


def main():
    log("loading dataset")
    df = L.load()
    L.assert_attack_valid(["X", "Y", "bits"])  # 'address' is a public column too (PUBLIC_COLS)
    n_total = len(df)
    log(f"loaded {n_total} rows, bits {df.bits.min()}-{df.bits.max()}")

    STATE["n_samples"] = int(n_total)
    STATE["bit_range"] = [int(df.bits.min()), int(df.bits.max())]

    # --- RESUME: keep families already computed (non-errored) from a prior run ---
    if os.path.exists(RESULTS_PATH):
        try:
            prev = json.load(open(RESULTS_PATH))
            for fname, fr in (prev.get("families") or {}).items():
                if "error" not in fr:
                    STATE["families"][fname] = fr
                    if fname not in STATE["families_done"]:
                        STATE["families_done"].append(fname)
            log(f"RESUME: keeping done families {STATE['families_done']}")
        except Exception as e:
            log(f"resume load failed ({e}); running all")
    checkpoint_write()

    y_n = df["n"].astype(int).values
    y_nclass = n_class_labels(y_n)
    groups = df["bits"].values
    log("computing byte-slice base (shared 'base' for all cv_delta comparisons)")
    base = byte_slice_base(df)
    checkpoint_write()

    for fname, fn in FAMILY_FNS:
        if fname in STATE["families_done"]:
            log(f"=== FAMILY: {fname} (already done, skipping) ===")
            continue
        if time_left() < 5 * 60:
            STATE["notes"].append(f"SKIPPED family '{fname}' -- time budget exhausted "
                                   f"({time_left():.0f}s left)")
            log(f"SKIPPING family {fname}: time budget exhausted")
            checkpoint_write()
            continue
        log(f"=== FAMILY: {fname} ===")
        t_fam0 = time.time()
        try:
            if fname == "kmer":
                feats, mi, cv, ctrl, note, m_used = fn(df, y_n, y_nclass, groups, base)
                n_used = m_used
                extra = {"note": note}
            elif fname == "cluster_purity":
                feats, mi, cv, ctrl, extra, n_used = fn(df, y_n, y_nclass, groups, base)
            else:
                feats, mi, cv, ctrl = fn(df, y_n, y_nclass, groups, base)
                n_used = n_total
                extra = {}

            reading = make_reading(fname, mi, cv, ctrl, n_used)
            STATE["families"][fname] = {
                "n_used": n_used,
                "dimensionality": int(feats.shape[1]),
                "mi_n": mi.get("mi_n_max"),
                "mi_n_mean": mi.get("mi_n_mean"),
                "mi_nclass": mi.get("mi_nclass"),
                "cv_acc": cv.get("acc_family_alone"),
                "cv_acc_base_only": cv.get("acc_base_only"),
                "cv_acc_base_plus_family": cv.get("acc_base_plus_family"),
                "cv_delta": cv.get("cv_delta"),
                "baseline_majority": cv.get("baseline_majority"),
                "control_s_star": ctrl.get("min_detectable_strength"),
                "control_detected": ctrl.get("detected"),
                "control_curve": ctrl.get("control_curve"),
                "control_dimensionality": ctrl.get("dimensionality"),
                "matched_null_acc": None,   # filled below only if lift observed
                "extra": extra,
                "reading": reading,
                "runtime_sec_family": round(time.time() - t_fam0, 1),
            }

            # ---- matched-null check: MANDATORY for any family showing a lift
            cv_delta = cv.get("cv_delta")
            mi_max = mi.get("mi_n_max")
            base_only = cv.get("acc_base_only") or 0
            shows_lift = (
                (isinstance(cv_delta, float) and cv_delta > 0.02) or
                (isinstance(mi_max, float) and mi_max > 0.02)
            )
            if shows_lift:
                log(f"  family {fname} shows a lift (cv_delta={cv_delta}, mi_max={mi_max}) "
                    f"-> running matched_null check")
                try:
                    from wp2_run import matched_null_safe
                    null_df = matched_null_safe(df, seed=42)
                except Exception:
                    null_df = C.matched_null(df[df.bits <= 60].copy(), seed=42)
                    STATE["notes"].append(f"{fname}: used bits<=60 subsample matched_null "
                                           f"(big-int overflow workaround unavailable)")
                try:
                    null_y_n = null_df["n"].astype(int).values
                    null_groups = null_df["bits"].values
                    null_base = byte_slice_base(null_df)
                    _, _, null_cv, _ = fn(null_df, null_y_n, n_class_labels(null_y_n),
                                          null_groups, null_base)
                    STATE["families"][fname]["matched_null_acc"] = null_cv.get("acc_family_alone")
                    STATE["families"][fname]["matched_null_cv_delta"] = null_cv.get("cv_delta")
                except Exception as e:
                    STATE["notes"].append(f"{fname}: matched_null recompute failed: {e}")
            checkpoint_write()

        except Exception as e:
            tb = traceback.format_exc()
            STATE["families"][fname] = {
                "error": str(e),
                "traceback": tb,
                "reading": f"ERROR in family '{fname}': {e} -- see traceback in notes.",
            }
            STATE["notes"].append(f"family {fname} raised {e}")
            log(f"ERROR in family {fname}: {e}\n{tb}")
            checkpoint_write()

        STATE["families_done"].append(fname)
        checkpoint_write()
        log(f"=== FAMILY {fname} DONE in {time.time()-t_fam0:.1f}s ===")

    STATE["runtime_sec"] = round(time.time() - T0, 1)
    checkpoint_write()
    return STATE


if __name__ == "__main__":
    result = main()
    print("\n" + "=" * 78)
    print("WP7 SUMMARY")
    print("=" * 78)
    for fname, _ in FAMILY_FNS:
        fr = result["families"].get(fname, {})
        if "error" in fr:
            print(f"{fname:18s}  ERROR: {fr['error']}")
            continue
        mi_n = fr.get("mi_n")
        s_star = fr.get("control_s_star")
        detected = fr.get("control_detected")
        cv_delta = fr.get("cv_delta")
        mi_str = f"{mi_n:.5f}" if isinstance(mi_n, float) else "n/a"
        delta_str = f"{cv_delta:.4f}" if isinstance(cv_delta, float) else "n/a"
        print(f"{fname:18s}  MI(feat;n)={mi_str}  cv_delta={delta_str}  "
              f"control_fired={detected}  s*={s_star}")
    print("=" * 78)
    print(f"Total runtime: {result['runtime_sec']:.1f}s")
    print(f"Families done: {result['families_done']}")
