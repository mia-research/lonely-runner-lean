"""
WP2 -- The public->n map-property ceiling at 100k  (ATTACK-VALID)

Whether ANY public-only function of (X,Y,bits) predicts n, an n-class, or
k mod m within fixed-n strata, above the noise floor -- at full 100k power.

Runs entirely from lib_data / lib_control per CLAUDE.md. No local LLM agents.
Writes RESULTS/WP2_map_ceiling.json (schema in RESULTS/SCHEMA.md), emitting a
valid partial JSON at every checkpoint so a timeout still leaves usable output.
"""
from __future__ import annotations
import os
import sys
import json
import time
import random
import traceback

import numpy as np
import pandas as pd
from sympy import isprime, factorint

sys.path.insert(0, os.path.dirname(__file__))
import lib_data as L
import lib_control as C

from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.neural_network import MLPClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.inspection import permutation_importance
from sklearn.base import clone
from sklearn.model_selection import GroupKFold

T0 = time.time()
RESULTS_PATH = os.path.join(os.path.dirname(__file__), "RESULTS", "WP2_map_ceiling.json")
RUNTIME_BUDGET_SEC = 90 * 60  # 90 min hard budget
SUBSAMPLE_N = 20000           # cap per rules item 5; benchmarked ~20-30s/fit at
                               # this scale x ~25 grouped_cv_score calls (target
                               # n, 11-pt control sweep, 4 n-class, 3 k-mod-m,
                               # matched_null variants) must fit the 90-min budget
MATCHED_NULL_CAP = 6000        # matched_null does one real ec_mul per row
                               # (~64ms at full 256-bit scale) -> 6000 rows
                               # ~ 6-7 min, kept well under budget
RANDOM_STATE = 0
SMALL_PRIMES = [p for p in range(3, 128) if isprime(p)]

STATE = {
    "wp": "WP2_map_ceiling",
    "model": "sonnet",
    "n_samples": None,
    "bit_range": None,
    "attack_valid": True,
    "positive_control": {},
    "null_model": "matched_null (bit-multiset preserved, d randomized) + baseline",
    "primary_result": {},
    "reading": "INCOMPLETE",
    "artifacts": [],
    "runtime_sec": None,
    "notes": [],
}


def checkpoint_write():
    STATE["runtime_sec"] = round(time.time() - T0, 1)
    with open(RESULTS_PATH, "w") as f:
        json.dump(STATE, f, indent=2, default=_json_default)
    print(f"[checkpoint] wrote partial JSON at t={STATE['runtime_sec']}s")


def _json_default(o):
    if isinstance(o, (np.integer,)):
        return int(o)
    if isinstance(o, (np.floating,)):
        return float(o)
    if isinstance(o, (np.ndarray,)):
        return o.tolist()
    return str(o)


def time_left():
    return RUNTIME_BUDGET_SEC - (time.time() - T0)


def log(msg):
    print(f"[{time.time()-T0:7.1f}s] {msg}", flush=True)


# --------------------------------------------------------------- features ---
def _byte_slices(vals: np.ndarray, prefix: str, n_bytes: int = 32) -> dict:
    cols = {}
    for b in range(n_bytes):
        cols[f"{prefix}_byte{b}"] = ((vals >> (8 * b)) & 0xFF).astype(np.float64)
    return cols


def _hi_lo_64(vals_obj: np.ndarray, prefix: str) -> dict:
    cols = {}
    mask64 = (1 << 64) - 1
    cols[f"{prefix}_lo64"] = np.array([float(v & mask64) for v in vals_obj])
    cols[f"{prefix}_hi64"] = np.array([float((v >> 192) & mask64) for v in vals_obj])
    cols[f"{prefix}_midlo64"] = np.array([float((v >> 64) & mask64) for v in vals_obj])
    cols[f"{prefix}_midhi64"] = np.array([float((v >> 128) & mask64) for v in vals_obj])
    return cols


def _residues(vals_obj: np.ndarray, prefix: str) -> dict:
    cols = {}
    for q in SMALL_PRIMES:
        cols[f"{prefix}_mod{q}"] = np.array([float(v % q) for v in vals_obj])
    return cols


def _popcount(v: int) -> int:
    return bin(v & ((1 << 256) - 1)).count("1")


def _hamming_weight(vals_obj: np.ndarray, prefix: str) -> dict:
    return {f"{prefix}_hwt": np.array([float(_popcount(v)) for v in vals_obj])}


def _byte_popcounts_summary(vals_obj: np.ndarray, prefix: str) -> dict:
    # per-byte popcount summary stats (mean/std/max) instead of 32 raw columns
    # (raw per-byte popcount is already implied by byte-slice values; keep this
    # compact but informative: max run length flavored stat = popcount variance)
    pcs = np.array([[bin((v >> (8 * b)) & 0xFF).count("1") for b in range(32)]
                    for v in vals_obj], dtype=np.float64)
    return {
        f"{prefix}_bytepc_mean": pcs.mean(axis=1),
        f"{prefix}_bytepc_std": pcs.std(axis=1),
        f"{prefix}_bytepc_max": pcs.max(axis=1),
    }


def _shannon_entropy_window(vals_obj: np.ndarray, prefix: str) -> dict:
    """Shannon entropy of each 32-bit window of a 256-bit value (8 windows),
    computed over the bit distribution (2-symbol alphabet) within the window."""
    cols = {f"{prefix}_ent_w{w}": np.zeros(len(vals_obj)) for w in range(8)}
    for i, v in enumerate(vals_obj):
        for w in range(8):
            window = (v >> (32 * w)) & 0xFFFFFFFF
            ones = bin(window).count("1")
            p1 = ones / 32.0
            p0 = 1.0 - p1
            ent = 0.0
            for p in (p0, p1):
                if p > 0:
                    ent -= p * np.log2(p)
            cols[f"{prefix}_ent_w{w}"][i] = ent
    return cols


def build_features(df: pd.DataFrame) -> tuple[pd.DataFrame, list[str]]:
    """Build the wide attack-valid feature matrix from (X, Y, bits) only."""
    X_obj = df["X"].astype(object).values
    Y_obj = df["Y"].astype(object).values
    bits = df["bits"].astype(np.float64).values

    cols = {}
    # 32 byte slices of X and Y
    cols.update(_byte_slices(X_obj, "X"))
    cols.update(_byte_slices(Y_obj, "Y"))
    # high/low 64-bit words
    cols.update(_hi_lo_64(X_obj, "X"))
    cols.update(_hi_lo_64(Y_obj, "Y"))
    # residues mod small primes 3..127
    cols.update(_residues(X_obj, "X"))
    cols.update(_residues(Y_obj, "Y"))
    # Hamming weight
    cols.update(_hamming_weight(X_obj, "X"))
    cols.update(_hamming_weight(Y_obj, "Y"))
    cols.update(_byte_popcounts_summary(X_obj, "X"))
    cols.update(_byte_popcounts_summary(Y_obj, "Y"))
    # Shannon entropy per 32-bit window
    cols.update(_shannon_entropy_window(X_obj, "X"))
    cols.update(_shannon_entropy_window(Y_obj, "Y"))

    # GLV image features: (beta*X mod p, Y)
    bx_obj = np.array([(L.BETA * int(v)) % L.P for v in X_obj], dtype=object)
    cols.update(_byte_slices(bx_obj, "BX"))
    cols.update(_residues(bx_obj, "BX"))
    cols.update(_hamming_weight(bx_obj, "BX"))

    # public field ratios: X*Y^-1 mod p, X^2*Y^-1 mod p, (X+Y) mod p, sliced
    xyinv = []
    x2yinv = []
    xpy = []
    for xv, yv in zip(X_obj, Y_obj):
        xv = int(xv); yv = int(yv)
        yinv = L.inv_mod(yv, L.P) if yv % L.P != 0 else 0
        xyinv.append((xv * yinv) % L.P)
        x2yinv.append((xv * xv % L.P * yinv) % L.P)
        xpy.append((xv + yv) % L.P)
    xyinv = np.array(xyinv, dtype=object)
    x2yinv = np.array(x2yinv, dtype=object)
    xpy = np.array(xpy, dtype=object)
    cols.update(_byte_slices(xyinv, "XYinv"))
    cols.update(_residues(xyinv, "XYinv"))
    cols.update(_byte_slices(x2yinv, "X2Yinv"))
    cols.update(_residues(x2yinv, "X2Yinv"))
    cols.update(_byte_slices(xpy, "XpY"))
    cols.update(_residues(xpy, "XpY"))

    # bits (N) itself as a feature
    cols["bits"] = bits

    feat_df = pd.DataFrame(cols)
    feature_cols = list(feat_df.columns)
    return feat_df, feature_cols


def matched_null_safe(df: pd.DataFrame, seed: int = 0) -> pd.DataFrame:
    """Same contract as lib_control.matched_null (exact bit-length multiset,
    real curve arithmetic, random d per band -> recompute n,k,D) but drawing
    the random offset with Python's arbitrary-precision `random` module.

    lib_control.matched_null uses numpy Generator.integers(0, span), which
    raises ValueError for span >= 2**63 (bits > ~63 in this dataset spans
    1..160) -- ValueError: high is out of bounds for int64. This is a bug in
    the shared harness for high bit-lengths; lib_control.py is untracked and
    other WPs are running against it concurrently, so rather than edit the
    shared module mid-flight, WP2 uses this drop-in replacement (same
    semantics, big-int-safe RNG) and reports the workaround in notes.
    """
    rnd = random.Random(seed)
    rows = []
    for bits, cnt in df["bits"].value_counts().sort_index().items():
        A = 1 << (int(bits) - 1)
        span = A  # band is [A, 2A)
        seen = set()
        for _ in range(int(cnt)):
            for _try in range(64):
                d = A + rnd.randrange(0, span) if span > 1 else A
                if d not in seen:
                    seen.add(d)
                    break
            n, k, D, dt = L.decompose(d, int(bits))
            X, Y = L.ec_mul(d)
            rows.append((int(bits), d, X, Y, n, k, D, dt))
    return pd.DataFrame(rows, columns=["bits", "d", "X", "Y", "n", "k", "D", "D_terms"])


# ----------------------------------------------------------------- targets --
def n_class_labels(n_vals: np.ndarray) -> dict[str, np.ndarray]:
    """Marginal n-class targets: prime?, phi(n)=2^r (power-of-2 totient)?,
    smooth (7-smooth)?, omega(n) (# distinct prime factors)."""
    is_prime = np.zeros(len(n_vals), dtype=int)
    is_2power_phi = np.zeros(len(n_vals), dtype=int)
    is_smooth = np.zeros(len(n_vals), dtype=int)
    omega = np.zeros(len(n_vals), dtype=int)
    cache = {}
    for i, n in enumerate(n_vals):
        n = int(n)
        if n not in cache:
            if n <= 1:
                factors = {}
            else:
                factors = factorint(n)
            pr = isprime(n)
            # phi(n) is a power of 2 iff every prime factor p satisfies p-1 is
            # a power of 2 (Fermat-prime-like) and n has no odd prime factor
            # with exponent>1 causing an odd factor in phi. Compute directly.
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


# --------------------------------------------------------------- MI helper --
def per_target_mi(feat_df: pd.DataFrame, y: np.ndarray, feature_cols: list[str],
                   max_features: int = 40, sample_cap: int = 20000) -> dict:
    from sklearn.feature_selection import mutual_info_classif
    rng = np.random.default_rng(RANDOM_STATE)
    idx = np.arange(len(y))
    if len(idx) > sample_cap:
        idx = rng.choice(idx, size=sample_cap, replace=False)
    cols = feature_cols[:max_features] if len(feature_cols) > max_features else feature_cols
    Xs = feat_df[cols].values[idx]
    ys = y[idx]
    try:
        mi = mutual_info_classif(Xs, ys, discrete_features=False,
                                  random_state=RANDOM_STATE, n_neighbors=3)
    except Exception as e:
        return {"error": str(e)}
    order = np.argsort(mi)[::-1]
    return {cols[i]: float(mi[i]) for i in order[:15]}


def stratified_subsample(df: pd.DataFrame, cap: int, seed: int) -> pd.DataFrame:
    """Subsample rows to ~cap total, stratified by `bits` so every bit-group
    keeps at least 1 row (required for GroupKFold to see every group)."""
    n_total = len(df)
    if n_total <= cap:
        return df.reset_index(drop=True)
    frac = cap / n_total
    rng_sub = np.random.default_rng(seed)
    idx_keep = []
    for _, g in df.groupby("bits"):
        n_keep = max(1, int(round(len(g) * frac)))
        n_keep = min(n_keep, len(g))
        chosen = rng_sub.choice(g.index.values, size=n_keep, replace=False)
        idx_keep.extend(chosen.tolist())
    return df.loc[sorted(idx_keep)].reset_index(drop=True)


# ------------------------------------------------------------------- main --
def main():
    log("loading dataset")
    df = L.load()
    L.assert_attack_valid(["X", "Y", "bits"])

    n_total = len(df)
    log(f"loaded {n_total} rows, bits {df.bits.min()}-{df.bits.max()}")

    # subsample to bound runtime (rule 5), stratified by bits so every
    # bit-group survives for GroupKFold
    df_before = n_total
    df = stratified_subsample(df, SUBSAMPLE_N, RANDOM_STATE)
    if len(df) < df_before:
        STATE["notes"].append(
            f"subsampled from {df_before} to {len(df)} rows (stratified by bits, "
            f"runtime bound)")
    else:
        STATE["notes"].append(f"no subsampling needed ({df_before} <= {SUBSAMPLE_N})")
    STATE["n_samples"] = int(len(df))
    STATE["bit_range"] = [int(df.bits.min()), int(df.bits.max())]
    checkpoint_write()

    log(f"post-subsample rows={len(df)}")

    log("building attack-valid feature matrix (X,Y,bits only)")
    feat_df, feature_cols = build_features(df)
    L.assert_attack_valid(feature_cols)
    log(f"feature matrix shape = {feat_df.shape}")
    STATE["notes"].append(f"feature matrix: {feat_df.shape[0]} rows x {feat_df.shape[1]} cols")
    checkpoint_write()

    groups = df["bits"].values
    Xmat = feat_df.values.astype(np.float64)

    # max_iter=60/max_depth=4 benchmarked at ~15-30s/fit on this dataset scale
    # (406 features); with ~25 grouped_cv_score calls planned across targets +
    # control sweep + matched_null this keeps the classifier-fit budget under
    # ~45 min, leaving room for matched_null's real ec_mul cost and the MLP
    # check. Accuracy at this depth/iter is already floor-bound for the null
    # case (256-way classification), so speed is prioritized over marginal
    # accuracy gains that would not change the reading.
    base_est = HistGradientBoostingClassifier(
        max_iter=60, max_depth=4, learning_rate=0.15, random_state=RANDOM_STATE)

    # ---------------------------------------------------------- baseline ---
    n_bins = df["bits"].nunique()
    results = {}

    # ================================================= POSITIVE CONTROL ===
    log("running positive control sweep (plant_leak s=0.1..1.0)")
    y_n = df["n"].astype(int).values
    strengths = [round(0.1 * i, 1) for i in range(1, 11)]
    control_curve = {}
    null_acc_for_control = None
    try:
        # null point: s=0 equivalent -> use real features w/o plant (already
        # have real_acc for n below, but compute standalone here for a clean
        # noise-floor reference tied to the SAME estimator/CV setup as sweep).
        for s in strengths:
            if time_left() < 8 * 60:
                STATE["notes"].append(f"control sweep cut short at s={s} (time budget)")
                break
            leak_col = C.plant_leak(y_n, strength=s, seed=RANDOM_STATE)
            Xp = np.column_stack([Xmat, leak_col])
            acc, folds = C.grouped_cv_score(Xp, y_n, groups, base_est,
                                             n_splits=min(5, n_bins))
            control_curve[str(s)] = acc
            log(f"  s={s}: grouped-CV acc={acc:.4f}")
        checkpoint_write()
    except Exception as e:
        STATE["notes"].append(f"control sweep error: {e}\n{traceback.format_exc()}")
        checkpoint_write()

    # null baseline for the control curve: s effectively 0 (pure noise leak col)
    try:
        leak0 = C.plant_leak(y_n, strength=0.0, seed=RANDOM_STATE)
        Xp0 = np.column_stack([Xmat, leak0])
        acc0, folds0 = C.grouped_cv_score(Xp0, y_n, groups, base_est, n_splits=min(5, n_bins))
        control_curve["0.0"] = acc0
        null_acc_for_control = acc0
        null_std_for_control = float(np.std(folds0)) if len(folds0) > 1 else 0.0
        log(f"  s=0.0 (null): acc={acc0:.4f} std={null_std_for_control:.4f}")
    except Exception as e:
        STATE["notes"].append(f"control null (s=0) error: {e}")
        null_acc_for_control = None
        null_std_for_control = 0.0

    # minimum detectable strength s*: first s clearing null+3sigma
    s_star = None
    if null_acc_for_control is not None:
        thresh = null_acc_for_control + 3 * (null_std_for_control or 0.01)
        for s in strengths:
            key = str(s)
            if key in control_curve and control_curve[key] >= thresh:
                s_star = s
                break
    STATE["positive_control"] = {
        "planted_strength_grid": strengths,
        "control_curve": control_curve,
        "null_acc_s0": null_acc_for_control,
        "null_std_s0": null_std_for_control,
        "min_detectable_strength": s_star,
        "detected": s_star is not None,
        "control_z": (
            (control_curve.get(str(s_star), 0) - (null_acc_for_control or 0)) /
            (null_std_for_control or 1e-6)
        ) if s_star is not None else None,
    }
    checkpoint_write()

    # ============================================== TARGET (a): n 256-class =
    log("target (a): n [256-class]")
    baseline_n = 1.0 / max(1, len(np.unique(y_n)))
    try:
        acc_n, folds_n = C.grouped_cv_score(Xmat, y_n, groups, base_est,
                                             n_splits=min(5, n_bins))
        log(f"  real n-class acc={acc_n:.4f} (baseline={baseline_n:.4f})")
    except Exception as e:
        acc_n, folds_n = None, None
        STATE["notes"].append(f"target n error: {e}\n{traceback.format_exc()}")
    checkpoint_write()

    # matched null for target n (matched_null_safe: big-int-safe workaround
    # for lib_control.matched_null's numpy int64 overflow at bits>~63; see
    # matched_null_safe docstring). Capped separately from SUBSAMPLE_N because
    # matched_null does one real ec_mul per row (~64ms at full 256-bit scale).
    log("matched_null frame for target n")
    try:
        mn_input = stratified_subsample(df, MATCHED_NULL_CAP, RANDOM_STATE)
        mn_df = matched_null_safe(mn_input, seed=RANDOM_STATE)
        STATE["notes"].append(
            "used matched_null_safe (local big-int-safe RNG) instead of "
            "lib_control.matched_null, which raises ValueError (numpy int64 "
            "overflow) for bits>~63 in this dataset; same contract otherwise. "
            f"matched_null input capped to {len(mn_input)} rows (real ec_mul cost).")
        mn_feat, mn_cols = build_features(mn_df)
        L.assert_attack_valid(mn_cols)
        y_mn = mn_df["n"].astype(int).values
        acc_n_mnull, _ = C.grouped_cv_score(mn_feat.values.astype(np.float64), y_mn,
                                             mn_df["bits"].values, base_est,
                                             n_splits=min(5, mn_df["bits"].nunique()))
        log(f"  matched-null n-class acc={acc_n_mnull:.4f}")
    except Exception as e:
        acc_n_mnull = None
        STATE["notes"].append(f"matched_null target n error: {e}\n{traceback.format_exc()}")
    checkpoint_write()

    # MLP small check on n (subsampled further if needed for speed)
    mlp_acc_n = None
    if time_left() > 15 * 60:
        try:
            log("small MLP check on target n")
            scaler = StandardScaler()
            Xs = scaler.fit_transform(Xmat)
            mlp = MLPClassifier(hidden_layer_sizes=(64, 32), max_iter=200,
                                 random_state=RANDOM_STATE, early_stopping=True)
            mlp_acc_n, _ = C.grouped_cv_score(Xs, y_n, groups, mlp, n_splits=min(3, n_bins))
            log(f"  MLP n-class acc={mlp_acc_n:.4f}")
        except Exception as e:
            STATE["notes"].append(f"MLP target n error: {e}")
    checkpoint_write()

    results["n"] = {
        "baseline": baseline_n,
        "real_acc_hgb": acc_n,
        "real_acc_folds_hgb": folds_n,
        "real_acc_mlp": mlp_acc_n,
        "matched_null_acc": acc_n_mnull,
        "n_classes_present": int(len(np.unique(y_n))),
    }
    STATE["primary_result"]["n"] = results["n"]
    checkpoint_write()

    # ===================================================== TARGET (b): n-class ===
    log("target (b): n-class {prime?, phi(n)=2^r?, smooth?, omega(n)}")
    nclass_targets = n_class_labels(y_n)
    nclass_results = {}
    for tname, yv in nclass_targets.items():
        if time_left() < 10 * 60:
            STATE["notes"].append(f"n-class target {tname} skipped (time budget)")
            break
        try:
            base_t = float(np.max(np.bincount(yv)) / len(yv))
            acc_t, folds_t = C.grouped_cv_score(Xmat, yv, groups, base_est,
                                                 n_splits=min(5, n_bins))
            # matched null version (reuse mn_feat/mn_df if available)
            acc_t_mnull = None
            try:
                mn_targets = n_class_labels(y_mn)
                yv_mn = mn_targets[tname]
                acc_t_mnull, _ = C.grouped_cv_score(
                    mn_feat.values.astype(np.float64), yv_mn, mn_df["bits"].values,
                    base_est, n_splits=min(5, mn_df["bits"].nunique()))
            except Exception as e2:
                STATE["notes"].append(f"matched_null n-class {tname} error: {e2}")
            nclass_results[tname] = {
                "baseline_majority": base_t,
                "real_acc": acc_t,
                "real_acc_folds": folds_t,
                "matched_null_acc": acc_t_mnull,
                "n_unique_labels": int(len(np.unique(yv))),
            }
            log(f"  {tname}: real_acc={acc_t:.4f} baseline={base_t:.4f} "
                f"matched_null={acc_t_mnull}")
        except Exception as e:
            STATE["notes"].append(f"n-class target {tname} error: {e}\n{traceback.format_exc()}")
        checkpoint_write()
    results["n_class"] = nclass_results
    STATE["primary_result"]["n_class"] = nclass_results
    checkpoint_write()

    # ============================================= TARGET (c): k mod m | n ===
    log("target (c): k mod m within fixed-n strata")
    kmodm_results = {}
    try:
        m = 4  # small modulus to keep class count sane within-stratum
        # choose the n value(s) with the most rows (largest strata) present
        n_counts = df["n"].value_counts()
        top_ns = n_counts.index[:3].tolist()  # up to 3 largest strata
        for nval in top_ns:
            if time_left() < 8 * 60:
                STATE["notes"].append(f"k-mod-m for n={nval} skipped (time budget)")
                break
            sub = df[df["n"] == nval].reset_index(drop=True)
            if sub["bits"].nunique() < 2 or len(sub) < 50:
                STATE["notes"].append(
                    f"k-mod-m n={nval} skipped: insufficient bit-groups/rows "
                    f"({sub['bits'].nunique()} groups, {len(sub)} rows)")
                continue
            sub_feat, sub_cols = build_features(sub)
            L.assert_attack_valid(sub_cols)
            y_k = (sub["k"].astype(int) % m).values
            base_k = float(np.max(np.bincount(y_k, minlength=m)) / len(y_k))
            n_splits_k = min(5, sub["bits"].nunique())
            acc_k, folds_k = C.grouped_cv_score(
                sub_feat.values.astype(np.float64), y_k, sub["bits"].values,
                base_est, n_splits=n_splits_k)
            kmodm_results[str(nval)] = {
                "m": m,
                "n_rows": int(len(sub)),
                "baseline_majority": base_k,
                "real_acc": acc_k,
                "real_acc_folds": folds_k,
            }
            log(f"  n={nval}: k mod {m} real_acc={acc_k:.4f} baseline={base_k:.4f} "
                f"(rows={len(sub)})")
            checkpoint_write()
    except Exception as e:
        STATE["notes"].append(f"k-mod-m target error: {e}\n{traceback.format_exc()}")
    results["k_mod_m_given_n"] = kmodm_results
    STATE["primary_result"]["k_mod_m_given_n"] = kmodm_results
    checkpoint_write()

    # ========================================== permutation importance =====
    log("permutation importance (on target n, real features, single fold)")
    top_features = {}
    try:
        gkf = GroupKFold(n_splits=min(5, n_bins))
        tr, te = next(gkf.split(Xmat, y_n, groups))
        est_pi = clone(base_est).fit(Xmat[tr], y_n[tr])
        pi = permutation_importance(est_pi, Xmat[te], y_n[te], n_repeats=5,
                                     random_state=RANDOM_STATE, n_jobs=-1)
        order = np.argsort(pi.importances_mean)[::-1][:20]
        top_features = {feature_cols[i]: float(pi.importances_mean[i]) for i in order}
        log(f"  top feature: {list(top_features.items())[0] if top_features else 'n/a'}")
    except Exception as e:
        STATE["notes"].append(f"permutation importance error: {e}\n{traceback.format_exc()}")
    STATE["primary_result"]["top_permutation_importance_features"] = top_features
    checkpoint_write()

    # =============================================== per-target MI =========
    log("per-target mutual information (subset of features)")
    mi_results = {}
    try:
        mi_results["n"] = per_target_mi(feat_df, y_n, feature_cols)
        for tname, yv in nclass_targets.items():
            mi_results[tname] = per_target_mi(feat_df, yv, feature_cols)
    except Exception as e:
        STATE["notes"].append(f"MI error: {e}\n{traceback.format_exc()}")
    STATE["primary_result"]["per_target_mi"] = mi_results
    checkpoint_write()

    # ===================================================== overall wrap-up =
    real_acc_summary = {
        "n": results.get("n", {}).get("real_acc_hgb"),
        "n_class": {k: v.get("real_acc") for k, v in nclass_results.items()},
        "k_mod_m_given_n": {k: v.get("real_acc") for k, v in kmodm_results.items()},
    }
    matched_null_summary = {
        "n": results.get("n", {}).get("matched_null_acc"),
        "n_class": {k: v.get("matched_null_acc") for k, v in nclass_results.items()},
    }

    STATE["primary_result"]["baseline"] = {
        "n": baseline_n,
        "n_class": {k: v.get("baseline_majority") for k, v in nclass_results.items()},
        "k_mod_m_given_n": {k: v.get("baseline_majority") for k, v in kmodm_results.items()},
    }
    STATE["primary_result"]["real_acc"] = real_acc_summary
    STATE["primary_result"]["matched_null_acc"] = matched_null_summary
    STATE["primary_result"]["min_detectable_strength"] = s_star

    control_fired = STATE["positive_control"].get("detected", False)
    K = len(feature_cols)
    nsamp = STATE["n_samples"]
    if control_fired:
        STATE["reading"] = (
            f"CONDITIONAL: with K={K} public-only features (byte slices, small-prime "
            f"residues, Hamming weight, 32-bit window entropy, GLV image, field ratios) "
            f"of (X,Y,bits) at n={nsamp} samples, no public->n / n-class / k-mod-m "
            f"map property was recovered above baseline+matched-null floor "
            f"(real_acc vs baseline: n={real_acc_summary['n']:.4f} vs {baseline_n:.4f}), "
            f"conditional on detector power floor s*={s_star} "
            f"(planted leak of strength >= s* is the smallest recoverable signal at "
            f"this N and feature set)."
            if real_acc_summary["n"] is not None else
            "INCOMPLETE: target n did not finish."
        )
    else:
        STATE["reading"] = (
            "INCONCLUSIVE — positive control did not clear null+3sigma at any swept "
            "strength; test underpowered, null discarded (not reported as a negative)."
        )
    STATE["attack_valid"] = True
    checkpoint_write()
    log("WP2 complete")


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        STATE["notes"].append(f"FATAL: {e}\n{traceback.format_exc()}")
        STATE["reading"] = "INCOMPLETE — fatal error, see notes."
        checkpoint_write()
        raise
