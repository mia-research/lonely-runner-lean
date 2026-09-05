#!/usr/bin/env python3
"""
exclusion_eisenstein_norm_v1.py
================================================================

EXCLUSION experiment: does the Eisenstein lift norm s(x_d) = N(eis(x_d))/p provide
NON-TRIVIAL exclusion power against the secret scalar d on a CM j=0 curve?

Frame shift from prior work: prior tests measured MI(s; d) ≈ 0 (positive extraction).
MI ≈ 0 at finite n does NOT formally exclude conditional-distribution deviations
that could provide exclusion. This test is more sensitive for structured alternatives
(e.g., d≡0 mod 3 over-represented in s < 3/16 disk).

Structure:
  Part A — Structural linchpin gate: s < 3/16 ⇒ ε(X) = 0 (geometric theorem)
  Part B — Marginal exclusion: P(s(x_d) | d mod m) ≠ P(s(x_d))  [PRE-REGISTERED]
  Part C — Joint exclusion: (s_d, s_{2d}, s_{3d}) triple-bin χ²  [conditional on B null]

Exact integer arithmetic for Part A (structural). numpy for Parts B/C (statistical).
"""

import sys
import os
import math
import random
import json
import time
import numpy as np
from fractions import Fraction as Fr
from collections import Counter

# ---- infrastructure imports (all exist in btc_puzzle_investigation/) ----
# Script is at btc_puzzle_investigation/scratchpad/session_2026-08-11/;
# go up 2 dirs to reach btc_puzzle_investigation/.
_script_dir = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(os.path.dirname(_script_dir)))
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, enorm, rdiv
from int1_frame_operator_v1 import build as build_frame
from glv_fundamental_domain_law_v1 import cube_roots, make_lift


# ==========================================================================
# PRE-REGISTRATION  (printed before any computation, locked before results)
# ==========================================================================
PREREG = """
=== PRE-REGISTRATION: Eisenstein Lift Norm -> d-Exclusion Test ===
Date: 2026-08-11
Experiment: exclusion_eisenstein_norm_v1.py

H0 (Part B): P(s(x_d) <= t | d == r mod m) = P(s(x_d) <= t) for ALL t, r, m in {2,3,6}
H1: exists m, r, t such that the conditional CDF differs from the marginal.

Decision rule (Part B):
  - KS statistic D = sup_t |CDF_r(t) - CDF(t)| across residue classes r mod m
  - REJECT H0 iff: D >= 0.02 AND shuffle p-value < 0.01/3 (Bonferroni for m in {2,3,6})
  - DECLARE NULL iff: D < 0.02 OR shuffle p-value >= 0.01/3 for all m

Controls (Part B):
  1. SHUFFLE: permute d labels 10,000x, recompute max KS. Empirical p = frac(shuffles >= obs).
  2. PLANTED: synthetic data where d mod 3 -> s in [0,1/8]. Verify detector fires (positive control).
  3. FIRING: confirm non-trivial predicate exists (some d with s >= 3/16, some with eps != 0).

Power analysis:
  - Test curve: p ~ 10^5, n ~ 10^5. Per-class size n/m ~ 33,000.
  - KS detectable effect size delta >= 0.015 at alpha = 0.003, power >= 0.95.

Scope:
  - All tests at small prime p (n ~ 10^5). ~50 binary orders below secp256k1.
  - Results at this scale do NOT prove anything about 2^256.

H0 (Part C, conditional): the map d -> (bin(s_d), bin(s_{2d}), bin(s_{3d})) has
  uniformly-sized fibers: each of K^3 bins contains ~ n/K^3 d-values.
Decision (Part C): chi^2 > chi^2_{K^3-1, 0.99} AND shuffle p < 0.01 -> REJECT; else NULL.
================================================================
"""


# ==========================================================================
# Generic ECC arithmetic for arbitrary prime field (parameterized)
# ==========================================================================
class ECCurve:
    """Minimal ECC over F_p: y^2 = x^3 + a*x + b. Jacobian coordinates."""
    def __init__(self, p, a, b, Gx, Gy, n_order):
        self.p = p
        self.a = a
        self.b = b
        self.Gx = Gx
        self.Gy = Gy
        self.n = n_order

    def _dbl(self, P):
        X, Y, Z = P
        if Y == 0:
            return (0, 1, 0)
        pp = self.p
        A = (X * X) % pp
        B = (Y * Y) % pp
        C = (B * B) % pp
        D = (2 * (((X + B) * (X + B) - A - C))) % pp
        E = (3 * A) % pp
        F = (E * E) % pp
        X3 = (F - 2 * D) % pp
        Y3 = (E * (D - X3) - 8 * C) % pp
        Z3 = (2 * Y * Z) % pp
        return (X3, Y3, Z3)

    def _add(self, P1, P2):
        X1, Y1, Z1 = P1
        X2, Y2, Z2 = P2
        if Z1 == 0: return P2
        if Z2 == 0: return P1
        pp = self.p
        Z1Z1 = (Z1 * Z1) % pp
        Z2Z2 = (Z2 * Z2) % pp
        U1 = (X1 * Z2Z2) % pp
        U2 = (X2 * Z1Z1) % pp
        S1 = (Y1 * Z2 % pp * Z2Z2) % pp
        S2 = (Y2 * Z1 % pp * Z1Z1) % pp
        if U1 == U2:
            if S1 != S2:
                return (0, 1, 0)
            return self._dbl(P1)
        H = (U2 - U1) % pp
        r = (S2 - S1) % pp
        HH = (H * H) % pp
        HHH = (H * HH) % pp
        V = (U1 * HH) % pp
        X3 = (r * r - HHH - 2 * V) % pp
        Y3 = (r * (V - X3) - S1 * HHH) % pp
        Z3 = (Z1 * Z2 % pp * H) % pp
        return (X3, Y3, Z3)

    def scalar_mul(self, k, base=None):
        if base is None:
            base = (self.Gx, self.Gy, 1)
        R = (0, 1, 0)
        Q = base
        while k > 0:
            if k & 1:
                R = self._add(R, Q)
            Q = self._dbl(Q)
            k >>= 1
        X, Y, Z = R
        if Z == 0:
            return None
        pp = self.p
        zi = pow(Z, pp - 2, pp)
        zi2 = (zi * zi) % pp
        return ((X * zi2) % pp, (Y * zi2 * zi) % pp)

    def enumerate_all_points(self):
        """Return list of (d, x, y) for d=1..n-1 via incremental addition. O(n)."""
        pp = self.p
        G_jac = (self.Gx, self.Gy, 1)
        pts = []
        P = G_jac
        for d in range(1, self.n):
            X, Y, Z = P
            if Z == 0:
                pts.append((d, 0, 0))
            else:
                zi = pow(Z, pp - 2, pp)
                zi2 = (zi * zi) % pp
                x = (X * zi2) % pp
                y = (Y * zi2 % pp * zi) % pp
                pts.append((d, x, y))
            P = self._add(P, G_jac)
        return pts


# ==========================================================================
# Part A: Structural linchpin gate  s < 3/16 => eps(X) = 0
# (exact integer / Fraction arithmetic — no numpy needed)
# ==========================================================================
def part_a_linchpin():
    """Test the structural claim: for ALL X in F_p^*, s(X) < 3/16 => eps(X) = 0."""
    t0 = time.time()
    print("=" * 72)
    print("PART A — Structural Linchpin Gate: s < 3/16 => eps(X) = 0")
    print("=" * 72)

    THRESH = Fr(3, 16)
    P_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

    # --- small primes p == 1 mod 3 ---
    from sympy import isprime
    primes = []
    q = 1000
    while len(primes) < 8:
        if isprime(q) and q % 3 == 1:
            primes.append(q)
        q += 1

    rng = random.Random(12345)
    header = f"{'p':>7} {'p%12':>5} {'Pr[s<3/16]':>11} {'Pr[eps=0]':>10} {'viol':>6} {'smax':>7} {'shuf_viol':>10} fire?"
    print(header)
    print("-" * len(header))

    results_a = []
    all_pass = True
    for p in primes:
        eis, eps = build_frame(p)
        n_lt = 0; n_lt_core = 0; n_core = 0; n_tot = p - 1
        smax = Fr(0); viol = []; labels = []
        for X in range(1, p):
            w = eis(X)
            s = Fr(enorm(w), p)
            e = eps(X)
            if s > smax: smax = s
            if e == 0: n_core += 1
            if s < THRESH:
                n_lt += 1
                if e == 0: n_lt_core += 1
                else: viol.append((X, s, e))
            labels.append((s, e))

        exist_noncore = any(e != 0 for _, e in labels)
        exist_noncore_hi = any((s >= THRESH and e != 0) for s, e in labels)

        # negative label-shuffle control
        es = [e for _, e in labels]
        rng.shuffle(es)
        shuf_viol = sum(1 for (s, _), e in zip(labels, es) if s < THRESH and e != 0)

        gate_ok = (len(viol) == 0)
        fire = exist_noncore and exist_noncore_hi
        all_pass = all_pass and gate_ok and fire

        pr_lt = Fr(n_lt, n_tot)
        pr_core = Fr(n_core, n_tot)
        print(f"{p:>7} {p%12:>5} {float(pr_lt):>11.4f} {float(pr_core):>10.4f} "
              f"{len(viol):>6} {float(smax):>7.4f} {shuf_viol:>10} "
              f"{'Y' if fire else 'n':>4}")
        if viol:
            print(f"        VIOLATIONS: {viol[:5]}")

        results_a.append(dict(p=p, n_tot=n_tot, pr_lt=float(pr_lt), pr_core=float(pr_core),
                              nviol=len(viol), smax=float(smax), shuf_viol=shuf_viol,
                              gate_ok=gate_ok, fire=fire))

    print(f"\nGATE (0 violations every prime) AND FIRING (non-core exists): "
          f"{'PASS' if all_pass else 'FAIL'}")

    # --- secp256k1 sampled ---
    print("\n--- secp256k1 (p ~ 2^256), sampled 20,000 X ---")
    from int1_frame_operator_v1 import build_secp
    eiss, epss = build_secp()
    rng2 = random.Random(2024)
    N = 20000
    n_lt = n_lt_core = n_core = 0
    smax = Fr(0); nviol = 0; hi_noncore = 0
    for _ in range(N):
        X = rng2.randrange(1, P_SECP)
        s = Fr(enorm(eiss(X)), P_SECP)
        e = epss(X)
        if s > smax: smax = s
        if e == 0: n_core += 1
        if s < THRESH:
            n_lt += 1
            if e == 0: n_lt_core += 1
            else: nviol += 1
        elif e != 0:
            hi_noncore += 1

    secp_ok = (nviol == 0 and hi_noncore > 0)
    print(f"  N={N};  Pr[s<3/16]={n_lt/N:.4f}  Pr[eps=0]={n_core/N:.4f}  smax={float(smax):.4f}")
    print(f"  gate violations (s<3/16 & eps!=0) = {nviol}   firing (s>=3/16 & eps!=0) = {hi_noncore}")
    print(f"  => secp gate {'HOLDS' if secp_ok else 'CHECK'}")

    results_a.append(dict(p='secp256k1', N_sampled=N, pr_lt=n_lt/N, pr_core=n_core/N,
                          nviol=nviol, smax=float(smax), gate_ok=secp_ok))
    print(f"  Part A elapsed: {time.time() - t0:.1f}s")
    return results_a


# ==========================================================================
# Part B: Marginal exclusion — numpy-accelerated KS with permutation test
# ==========================================================================

def ks_two_class(s_arr, mask_r):
    """
    Fast KS statistic: D = sup_t |CDF_r(t) - CDF_other(t)|.
    s_arr: numpy array of s-values (in d-order, d=1..n).
    mask_r: boolean array, True where d is in class r.
    Returns: D (float).
    """
    n_r = mask_r.sum()
    n_other = len(mask_r) - n_r
    if n_r == 0 or n_other == 0:
        return 0.0
    order = np.argsort(s_arr, kind='mergesort')
    cum_r = np.cumsum(mask_r[order], dtype=np.float64)
    cum_other = np.cumsum(~mask_r[order], dtype=np.float64)
    d_max = np.max(np.abs(cum_r / n_r - cum_other / n_other))
    return float(d_max)


def ks_max_all_classes(s_arr, masks):
    """
    Compute max KS across all classes in a single sort pass.
    masks: dict {r: boolean_array} for each residue class.
    Returns: max D across all classes.
    """
    order = np.argsort(s_arr, kind='mergesort')
    d_max_global = 0.0
    for r, mask_r in masks.items():
        n_r = mask_r.sum()
        if n_r == 0:
            continue
        n_other = len(mask_r) - n_r
        if n_other == 0:
            continue
        cum_r = np.cumsum(mask_r[order], dtype=np.float64)
        cum_other = np.cumsum(~mask_r[order], dtype=np.float64)
        d_max = np.max(np.abs(cum_r / n_r - cum_other / n_other))
        if d_max > d_max_global:
            d_max_global = d_max
    return float(d_max_global)


def part_b_marginal_exclusion(pts, p, n, curve_name):
    """
    Test P(s(x_d) | d mod m) = P(s(x_d)) for m in {2,3,6}.
    pts: list of (d, x, y) tuples for d=1..n-1.
    PRE-REGISTERED: see PREREG block above.
    """
    t0 = time.time()
    print("\n" + "=" * 72)
    print(f"PART B — Marginal Exclusion: P(s | d mod m) on {curve_name}")
    print(f"  (p={p}, n={n}, {len(pts)} points)")
    print("=" * 72)

    eis_fn, _ = build_frame(p)

    # Compute s-values for all d (in d-order) as numpy array
    s_arr = np.empty(n - 1, dtype=np.float64)
    for i, (d, x, y) in enumerate(pts):
        w = eis_fn(x)
        s_arr[i] = float(Fr(enorm(w), p))

    N_SHUFFLES = 10000
    THRESH_KS = 0.02
    ALPHA_BONF = 0.01 / 3  # Bonferroni for m in {2,3,6}

    # Pre-build class masks (fixed: d mod m is determined by position)
    # d runs from 1 to n-1, so d = i+1 where i=0..n-2
    d_indices = np.arange(1, n)  # d values

    results_b = {}
    overall_null = True

    for m in [2, 3, 6]:
        print(f"\n  --- m = {m} (testing d mod {m} classes) ---")
        t_m = time.time()

        masks = {}
        for r in range(m):
            masks[r] = (d_indices % m == (r % m))

        # Compute KS for each residue class (observed)
        ks_obs = {}
        for r in range(m):
            d_stat = ks_two_class(s_arr, masks[r])
            ks_obs[r] = d_stat
            n_cls = int(masks[r].sum())
            print(f"    r={r}: KS = {d_stat:.6f}  (n_class={n_cls})")

        max_ks = max(ks_obs.values())
        print(f"    max KS = {max_ks:.6f}")

        # Shuffle control — numpy accelerated, single sort per shuffle
        rng_shuffle = np.random.RandomState(42 + m)
        n_shuffle_exceed = 0

        shuf_s = s_arr.copy()
        for si in range(N_SHUFFLES):
            rng_shuffle.shuffle(shuf_s)
            max_ks_shuf = ks_max_all_classes(shuf_s, masks)
            if max_ks_shuf >= max_ks:
                n_shuffle_exceed += 1
            if (si + 1) % 2500 == 0:
                print(f"    shuffle progress: {si+1}/{N_SHUFFLES}  "
                      f"(exceed so far: {n_shuffle_exceed})")

        p_value = (n_shuffle_exceed + 1) / (N_SHUFFLES + 1)
        print(f"    shuffle p-value ({N_SHUFFLES} perms) = {p_value:.6f}")
        print(f"    m={m} elapsed: {time.time() - t_m:.1f}s")

        reject = (max_ks >= THRESH_KS) and (p_value < ALPHA_BONF)
        label = "REJECT H0 (signal)" if reject else "NULL"
        if reject:
            overall_null = False
        print(f"    => {label}  (threshold: KS>={THRESH_KS} AND p<{ALPHA_BONF:.4f})")

        results_b[m] = dict(max_ks=max_ks, p_value=p_value, reject=reject,
                            ks_per_class={str(r): ks_obs[r] for r in range(m)})

    # Planted control (synthetic d-mod-3 -> s bias)
    print(f"\n  --- PLANTED CONTROL (synthetic bias: d%3==0 -> s in [0,1/8]) ---")
    rng_plant = np.random.RandomState(99)
    planted_s = np.empty(n - 1, dtype=np.float64)
    for i in range(n - 1):
        d = i + 1
        if d % 3 == 0:
            planted_s[i] = rng_plant.random() * (1.0 / 8)
        else:
            planted_s[i] = rng_plant.random() * 0.75
    masks_3 = {r: (d_indices % 3 == r) for r in range(3)}
    max_ks_plant = ks_max_all_classes(planted_s, masks_3)
    print(f"    planted max KS = {max_ks_plant:.6f}  (should be >> 0.02)")

    n_shuf_exceed_plant = 0
    rng_plant2 = np.random.RandomState(199)
    shuf_plant = planted_s.copy()
    for si in range(N_SHUFFLES):
        rng_plant2.shuffle(shuf_plant)
        mks = ks_max_all_classes(shuf_plant, masks_3)
        if mks >= max_ks_plant:
            n_shuf_exceed_plant += 1
    p_plant = (n_shuf_exceed_plant + 1) / (N_SHUFFLES + 1)
    print(f"    planted shuffle p-value = {p_plant:.6f}  (should be << 0.01)")
    print(f"    planted control {'FIRES' if max_ks_plant >= 0.02 and p_plant < 0.01 else 'FAILS'}")

    # Firing check
    n_disk = int((s_arr < 3.0 / 16.0).sum())
    _, eps_fn = build_frame(p)
    n_core = 0
    for d, x, y in pts:
        if eps_fn(x) == 0:
            n_core += 1
    n_total_noncore = (n - 1) - n_core
    print(f"\n  FIRING CHECK: {n_total_noncore} non-core points exist, "
          f"{n_disk}/{n-1} in disk")
    firing = (n_total_noncore > 0) and (n_disk < n - 1)
    print(f"  firing = {'YES' if firing else 'NO'}")

    print(f"\n  Part B total elapsed: {time.time() - t0:.1f}s")
    return dict(results_per_m=results_b, overall_null=overall_null,
                planted_ks=max_ks_plant, planted_p=p_plant,
                n=n, n_disk=n_disk, n_core=n_core, firing=firing)


# ==========================================================================
# Part C: Joint exclusion — (s_d, s_{2d}, s_{3d}) triple-bin chi^2
# ==========================================================================
def part_c_joint_exclusion(pts, p, n, curve_name, s_arr):
    """
    Test whether the triple (s_d, s_{2d}, s_{3d}) partitions d-space uniformly.
    s_arr: numpy array of s(x_d) in d-order (from Part B), length n-1.
    """
    t0 = time.time()
    print("\n" + "=" * 72)
    print("PART C \u2014 Joint Exclusion: (s_d, s_{{2d}}, s_{{3d}}) on "
          + curve_name)
    print(f"  (p={p}, n={n})")
    print("=" * 72)

    # Build x-lookup: x_at[k] = x-coordinate of [k]G for k=1..n-1
    # pts is 0-indexed: pts[i] = (i+1, x_{i+1}, y_{i+1})
    x_at = np.empty(n, dtype=np.int64)  # 1-indexed, x_at[0] unused
    for i, (d, x, y) in enumerate(pts):
        x_at[d] = x

    # Precompute s from x (cache for all x-values)
    eis_fn, _ = build_frame(p)
    s_from_x = {}
    for d in range(1, n):
        xd = x_at[d]
        if xd not in s_from_x:
            w = eis_fn(xd)
            s_from_x[xd] = float(Fr(enorm(w), p))

    K = 8  # number of bins per coordinate
    bin_width = (3.0 / 4.0) / K  # s ranges [0, 3/4]

    # Build triple bins using numpy for speed
    n_pts = n - 1
    b1_arr = np.minimum((s_arr / bin_width).astype(np.int32), K - 1)

    # s_{2d}: for d=1..n-1, 2d mod n (if result is 0, use n)
    d_arr = np.arange(1, n, dtype=np.int64)
    d2_arr = (2 * d_arr) % n
    d2_arr[d2_arr == 0] = n
    d3_arr = (3 * d_arr) % n
    d3_arr[d3_arr == 0] = n

    s2d_arr = np.array([s_from_x[int(x_at[d2])] for d2 in d2_arr], dtype=np.float64)
    s3d_arr = np.array([s_from_x[int(x_at[d3])] for d3 in d3_arr], dtype=np.float64)

    b2_arr = np.minimum((s2d_arr / bin_width).astype(np.int32), K - 1)
    b3_arr = np.minimum((s3d_arr / bin_width).astype(np.int32), K - 1)

    # Encode triple bin as single integer: b1 * K^2 + b2 * K + b3
    K2 = K * K
    triple_bins = b1_arr * K2 + b2_arr * K + b3_arr
    pair_bins = b1_arr * K + b2_arr

    # Count bins
    triple_counts = np.bincount(triple_bins, minlength=K ** 3)[:K ** 3].astype(np.float64)
    pair_counts = np.bincount(pair_bins, minlength=K ** 2)[:K ** 2].astype(np.float64)

    expected_triple = n_pts / (K ** 3)
    expected_pair = n_pts / (K ** 2)

    chi2_triple = float(np.sum((triple_counts - expected_triple) ** 2 / expected_triple))
    chi2_pair = float(np.sum((pair_counts - expected_pair) ** 2 / expected_pair))
    dof_triple = K ** 3 - 1  # 511
    dof_pair = K ** 2 - 1    # 63

    # Critical values
    try:
        from scipy.stats import chi2 as chi2_dist
        crit_triple = chi2_dist.ppf(0.99, dof_triple)
        crit_pair = chi2_dist.ppf(0.99, dof_pair)
        p_val_triple = 1 - chi2_dist.cdf(chi2_triple, dof_triple)
        p_val_pair = 1 - chi2_dist.cdf(chi2_pair, dof_pair)
    except ImportError:
        crit_triple = 586.1
        crit_pair = 93.0
        z_triple = (chi2_triple - dof_triple) / math.sqrt(2 * dof_triple)
        z_pair = (chi2_pair - dof_pair) / math.sqrt(2 * dof_pair)
        p_val_triple = 1 - (0.5 * (1 + math.erf(z_triple / math.sqrt(2))))
        p_val_pair = 1 - (0.5 * (1 + math.erf(z_pair / math.sqrt(2))))

    print(f"  K = {K} bins per coordinate, K^3 = {K**3} triple bins, K^2 = {K**2} pair bins")
    print(f"  expected per triple bin = {expected_triple:.1f}, per pair bin = {expected_pair:.1f}")
    print(f"\n  TRIPLE chi^2 = {chi2_triple:.2f},  dof = {dof_triple},  critical(0.99) = {crit_triple:.1f}")
    print(f"  p-value ~ {p_val_triple:.6f}")
    print(f"  => {'REJECT (non-uniform)' if chi2_triple > crit_triple else 'NULL (uniform)'}")
    print(f"\n  PAIR chi^2 = {chi2_pair:.2f},  dof = {dof_pair},  critical(0.99) = {crit_pair:.1f}")
    print(f"  p-value ~ {p_val_pair:.6f}")
    print(f"  => {'REJECT (non-uniform)' if chi2_pair > crit_pair else 'NULL (uniform)'}")

    # Shuffle control for triple (numpy accelerated)
    N_SHUF_C = 10000
    print(f"\n  Shuffle control ({N_SHUF_C} perms for triple)...")
    t_shuf = time.time()
    rng_c = np.random.RandomState(77)
    n_shuf_exceed = 0

    shuf_s = s_arr.copy()
    for si in range(N_SHUF_C):
        rng_c.shuffle(shuf_s)
        shuf_b1 = np.minimum((shuf_s / bin_width).astype(np.int32), K - 1)
        # For shuffled s, s_{2d} is shuf_s at position (2d mod n)-1
        shuf_b2 = np.minimum((shuf_s[d2_arr - 1] / bin_width).astype(np.int32), K - 1)
        shuf_b3 = np.minimum((shuf_s[d3_arr - 1] / bin_width).astype(np.int32), K - 1)
        shuf_triple = shuf_b1 * K2 + shuf_b2 * K + shuf_b3
        shuf_counts = np.bincount(shuf_triple, minlength=K**3)[:K**3].astype(np.float64)
        chi2_shuf = float(np.sum((shuf_counts - expected_triple) ** 2 / expected_triple))
        if chi2_shuf >= chi2_triple:
            n_shuf_exceed += 1
        if (si + 1) % 2500 == 0:
            print(f"    shuffle progress: {si+1}/{N_SHUF_C}  (exceed: {n_shuf_exceed})")

    p_shuf = (n_shuf_exceed + 1) / (N_SHUF_C + 1)
    print(f"  shuffle p-value = {p_shuf:.6f}")
    print(f"  shuffle elapsed: {time.time() - t_shuf:.1f}s")

    reject_triple = (chi2_triple > crit_triple) and (p_shuf < 0.01)
    reject_pair = chi2_pair > crit_pair
    print(f"\n  FINAL Part C triple: {'REJECT' if reject_triple else 'NULL'}")
    print(f"  FINAL Part C pair:   {'REJECT' if reject_pair else 'NULL'}")
    print(f"  Part C total elapsed: {time.time() - t0:.1f}s")

    return dict(chi2_triple=chi2_triple, p_val_triple=p_val_triple,
                chi2_pair=chi2_pair, p_val_pair=p_val_pair,
                crit_triple=crit_triple, crit_pair=crit_pair,
                p_shuf_triple=p_shuf,
                reject_triple=reject_triple,
                reject_pair=reject_pair)


# ==========================================================================
# Main
# ==========================================================================
def main():
    t_total = time.time()
    print(PREREG)

    # === Part A: Structural linchpin gate ===
    results_a = part_a_linchpin()

    # === Part B: Marginal exclusion ===
    # Small j=0 curve: p=100003, n=99667, G=(2, 13675), cofactor 1.
    p_small = 100003
    n_small = 99667
    Gx_small = 2
    Gy_small = 13675

    print("\n" + "=" * 72)
    print(f"Setting up test curve: y^2 = x^3 + 7 over F_{p_small}")
    print(f"  G = ({Gx_small}, {Gy_small}), order n = {n_small}")
    print(f"  Enumerating all {n_small-1} points [d]G for d=1..{n_small-1}...")
    print("=" * 72)

    curve = ECCurve(p_small, 0, 7, Gx_small, Gy_small, n_small)
    t_enum = time.time()
    pts = curve.enumerate_all_points()
    print(f"  Enumerated {len(pts)} points in {time.time() - t_enum:.1f}s")
    print(f"  First: d={pts[0][0]} x={pts[0][1]} y={pts[0][2]}")
    print(f"  Last:  d={pts[-1][0]} x={pts[-1][1]} y={pts[-1][2]}")

    # Verify: [n]G = O
    test_identity = curve.scalar_mul(n_small)
    print(f"  Verification: [{n_small}]G = {'O (identity)' if test_identity is None else 'FAIL'}")

    results_b = part_b_marginal_exclusion(pts, p_small, n_small,
                                            f"y^2=x^3+7 / F_{p_small}")

    # === Part C: Joint exclusion (conditional on Part B null) ===
    if results_b['overall_null']:
        print("\n  Part B was NULL -> proceeding to Part C (joint exclusion)")
        eis_fn, _ = build_frame(p_small)
        s_arr = np.empty(n_small - 1, dtype=np.float64)
        for i, (d, x, y) in enumerate(pts):
            w = eis_fn(x)
            s_arr[i] = float(Fr(enorm(w), p_small))
        results_c = part_c_joint_exclusion(pts, p_small, n_small,
                                            f"y^2=x^3+7 / F_{p_small}", s_arr)
    else:
        print("\n  Part B found signal -> Part C skipped (marginal exclusion already exists)")
        results_c = None

    # === Summary ===
    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)
    all_gate_ok = all(r.get('gate_ok', False) for r in results_a)
    print(f"  Part A (linchpin gate): {'PASS' if all_gate_ok else 'FAIL'}")
    print(f"  Part B (marginal exclusion): {'NULL' if results_b['overall_null'] else 'SIGNAL FOUND'}")
    if results_c is not None:
        print(f"  Part C (joint exclusion): {'NULL' if not results_c['reject_triple'] else 'SIGNAL FOUND'}")
    else:
        print(f"  Part C: SKIPPED (Part B had signal)")
    print(f"\n  Total elapsed: {time.time() - t_total:.1f}s")

    # JSON output
    output = {
        'prereg': 'printed above',
        'part_a': results_a,
        'part_b': {k: v for k, v in results_b.items() if k != 'results_per_m'},
        'part_b_per_m': results_b['results_per_m'],
        'part_c': results_c,
    }
    outpath = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           'exclusion_eisenstein_norm_v1_results.json')
    with open(outpath, 'w') as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\n  Results saved to: {outpath}")


if __name__ == "__main__":
    main()
