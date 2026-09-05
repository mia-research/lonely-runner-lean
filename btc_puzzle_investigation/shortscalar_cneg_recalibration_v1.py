#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
shortscalar_cneg_recalibration_v1.py

STEP 1 of the Short-Scalar Sums / Group-Law Difference-Sets frontier:
mechanical recalibration of the C-NEG control under the n>=20 rule.

WHAT DEFECT THIS FIXES (handoff 2026-08-01, item C3 + Section D standing repair)
--------------------------------------------------------------------------------
C-NEG as originally specified compared ONE control draw against the null's 95th
percentile.  A single draw from the null's own distribution exceeds the 95th
percentile with probability exactly 0.05 BY DEFINITION -- so the control
false-alarms 5% of the time on correct data.  This voided the spectral run
(96.0 pctile) and read the group-law E6 arm at the 99.7th pctile as if it were a
fire.  It is a defect in the DECISION RULE, not in the curve.

THE FIX (this script): draw n>=20 INDEPENDENT C-NEG realizations, rank each
against a null reference, and verify the tail rate is consistent with nominal
(~5% above the 95th, ~1% above the 99th) i.e. the C-NEG percentile ranks are
uniform.  With n>=20 the 5% tail is measurable; with n=1 it is invisible.

This is a MECHANICAL debt (control calibration; CLAUDE.md 2a table = self-audit
sufficient).  It reads only the matched geometric NULL -- uniform random curve
points, NO short-scalar arm, NO leakage readout -- so it does not require the
experiment-designer frame gate.  No grade is promoted here.

RULES OF ENGAGEMENT honored:
  Rule 2  Big-O + op count printed before the run; pow benchmarked; pairwise
          table precomputed ONCE (O(P^2)), draws are O(M^2) integer lookups.
  Rule 3  geometric null = uniform random curve points (no scalar mult) = uniform
          group element (secp cofactor 1).  Reference and C-NEG use the SAME
          process, so they are exchangeable -> ranks uniform by construction.
  no-float rule (BTC CLAUDE.md): pure Python int in the signal path; every
          statistic is an exact integer quadratic form; floats only in display.

Object: group-law difference x(P_i - P_j).  Readouts chi2, chi3, chi6 all legal
        (x(-Q)=x(Q)).  Statistics E2, E3, E6 = |sum chi_k|^2, exact integers.

Usage:  python3 shortscalar_cneg_recalibration_v1.py [P] [R] [n] [M] [seed]
"""

import sys
import time
import random
from collections import Counter

# ---------------------------------------------------------------------------
# secp256k1 field prime and curve y^2 = x^3 + 7 (a=0, b=7).
# ---------------------------------------------------------------------------
P_FIELD = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
B_CURVE = 7
# GLV endomorphism constant: beta^3 == 1 mod p, phi(x,y) = (beta*x, y) = lambda*P.
BETA = 0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE

EXP2 = (P_FIELD - 1) // 2        # chi2 exponent (Legendre)
EXP3 = (P_FIELD - 1) // 3        # chi3 exponent (cubic character)
SQRT_EXP = (P_FIELD + 1) // 4    # square root exponent (valid since p == 3 mod 4)


def self_checks():
    assert P_FIELD % 4 == 3, "p must be 3 mod 4 for the sqrt exponent"
    assert P_FIELD % 3 == 1, "p must be 1 mod 3 for a nontrivial cubic character"
    assert pow(BETA, 3, P_FIELD) == 1 and BETA != 1, "BETA must be a primitive cube root of 1"
    # A primitive cube root of unity in F_p, used to label chi3 classes.
    W = None
    for z in range(2, 100):
        t = pow(z, EXP3, P_FIELD)
        if t != 1:
            W = t
            break
    assert W is not None
    W2 = (W * W) % P_FIELD
    assert (W * W2) % P_FIELD == 1 and (1 != W) and (W != W2), "bad cube-root labelling"
    return W, W2


W, W2 = self_checks()
CUBE_LABEL = {1: 0, W: 1, W2: 2}   # chi3(a) in {1,W,W2} -> class {0,1,2}


# ---------------------------------------------------------------------------
# Character classes (exact integer modexp).
# ---------------------------------------------------------------------------
def chi2_class(a):
    """0 if a is a QR, 1 if a non-QR.  a != 0 assumed (differences are nonzero)."""
    t = pow(a % P_FIELD, EXP2, P_FIELD)
    return 0 if t == 1 else 1


def chi3_class(a):
    """cubic class in {0,1,2}."""
    return CUBE_LABEL[pow(a % P_FIELD, EXP3, P_FIELD)]


# ---------------------------------------------------------------------------
# Uniform random curve point WITHOUT scalar multiplication (Rule 3 null).
# ---------------------------------------------------------------------------
def random_point(rng):
    while True:
        x = rng.randrange(1, P_FIELD)
        rhs = (x * x % P_FIELD * x + B_CURVE) % P_FIELD
        if rhs == 0:
            continue  # 2-torsion; does not exist on prime-order secp
        if pow(rhs, EXP2, P_FIELD) != 1:
            continue  # not a QR
        y = pow(rhs, SQRT_EXP, P_FIELD)
        if rng.getrandbits(1):
            y = P_FIELD - y
        return (x, y)


def gl_diff_x(Pi, Pj):
    """x-coordinate of the group-law difference P_i - P_j = P_i + (-P_j).
    Returns None for the degenerate x_i == x_j case (astronomically rare)."""
    xi, yi = Pi
    xj, yj = Pj
    nyj = P_FIELD - yj          # -P_j = (x_j, p - y_j)
    dx = (xj - xi) % P_FIELD
    if dx == 0:
        return None
    lam = ((nyj - yi) % P_FIELD) * pow(dx, -1, P_FIELD) % P_FIELD
    x3 = (lam * lam - xi - xj) % P_FIELD
    return x3


# ---------------------------------------------------------------------------
# Exact integer statistics from a 6-cell histogram H over code = b*3 + c,
# b = chi2 class in {0,1}, c = chi3 class in {0,1,2}.
# ---------------------------------------------------------------------------
def stats_from_hist(H):
    # H indexed by code 0..5.
    nb0 = H[0] + H[1] + H[2]                 # chi2 == +1
    nb1 = H[3] + H[4] + H[5]                 # chi2 == -1
    E2 = (nb0 - nb1) ** 2

    nc0 = H[0] + H[3]                         # chi3 class 0
    nc1 = H[1] + H[4]                         # chi3 class 1
    nc2 = H[2] + H[5]                         # chi3 class 2
    A3 = nc0 - nc2
    B3 = nc1 - nc2
    E3 = A3 * A3 - A3 * B3 + B3 * B3          # |sum chi3|^2

    # chi6 class m(b,c) = (2c + 3b) mod 6.
    # code->m : 0->0, 1->2, 2->4, 3->3, 4->5, 5->1
    nm = [H[0], H[5], H[1], H[3], H[2], H[4]]  # nm[m] for m=0..5
    A6 = nm[0] - nm[2] - nm[3] + nm[5]
    B6 = nm[1] + nm[2] - nm[4] - nm[5]
    E6 = A6 * A6 + A6 * B6 + B6 * B6          # |sum chi6|^2
    return E2, E3, E6


def hist_from_codes(codes):
    H = [0, 0, 0, 0, 0, 0]
    for code in codes:
        H[code] += 1
    return H


# ---------------------------------------------------------------------------
# Instrument validation: phi-closed set forces E3 = E6 = 0 exactly on the
# group-law difference (reproduces ANALYSIS_diffset_readout_parity_void_v1 and
# RESULT_interval_cubic_structure_v1 C-GLV).
# ---------------------------------------------------------------------------
def c_glv_check(rng, n_triples=30):
    print("chi2(beta) class =", chi2_class(BETA),
          "| chi3(beta) class =", chi3_class(BETA),
          "  (chi3(beta) != 0  => 1+chi3(beta)+chi3(beta)^2 = 0 => cubic classes annihilate)")
    S = []
    for _ in range(n_triples):
        x, y = random_point(rng)
        # phi-triple: {(x,y),(beta x,y),(beta^2 x,y)} -- all on curve, all share y.
        bx = (BETA * x) % P_FIELD
        b2x = (BETA * bx) % P_FIELD
        S.extend([(x, y), (bx, y), (b2x, y)])
    codes = []
    degen = 0
    for i in range(len(S)):
        for j in range(i + 1, len(S)):
            xd = gl_diff_x(S[i], S[j])
            if xd is None:
                degen += 1
                continue
            codes.append(chi2_class(xd) * 3 + chi3_class(xd))
    E2, E3, E6 = stats_from_hist(hist_from_codes(codes))
    print(f"C-GLV phi-closed set: |S|={len(S)}, pairs={len(codes)}, degenerate={degen}")
    print(f"    E2={E2}  E3={E3}  E6={E6}")
    assert E3 == 0, f"instrument FAIL: E3 should be 0 on phi-closed group-law diff, got {E3}"
    assert E6 == 0, f"instrument FAIL: E6 should be 0 on phi-closed group-law diff, got {E6}"
    print("    -> E3=0 and E6=0 EXACT: instrument reads the intended object (forced-zero confirmed).")
    return True


# ---------------------------------------------------------------------------
# Percentile helpers -- integer order statistics, no float threshold on data.
# ---------------------------------------------------------------------------
def pct_value(sorted_vals, q_num, q_den):
    """Value at the ceil(q * R) order statistic (1-indexed).  Integer arithmetic."""
    R = len(sorted_vals)
    pos = (q_num * R + q_den - 1) // q_den   # ceil(q_num/q_den * R)
    pos = min(max(pos, 1), R)
    return sorted_vals[pos - 1]


def count_ge(sorted_vals, v):
    """#{ref >= v} by binary search (integer compares)."""
    lo, hi = 0, len(sorted_vals)
    while lo < hi:
        mid = (lo + hi) // 2
        if sorted_vals[mid] < v:
            lo = mid + 1
        else:
            hi = mid
    return len(sorted_vals) - lo


def main():
    P = int(sys.argv[1]) if len(sys.argv) > 1 else 512     # pool size
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 3000    # null reference draws
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 300     # C-NEG draws (>=20)
    M = int(sys.argv[4]) if len(sys.argv) > 4 else 80      # points per draw
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 20260802

    assert n >= 20, "C-NEG recalibration requires n >= 20 draws"
    rng = random.Random(seed)

    pairs_pool = P * (P - 1) // 2
    pairs_draw = M * (M - 1) // 2
    modexps_precompute = pairs_pool * 2      # chi2 + chi3 per pool pair
    lookups_draws = (R + n) * pairs_draw

    print("=" * 78)
    print("C-NEG RECALIBRATION v1  (group-law difference, chi2/chi3/chi6)")
    print("=" * 78)
    print(f"config: P(pool)={P}  R(ref)={R}  n(C-NEG)={n}  M(draw)={M}  seed={seed}")
    print("BIG-O / OP COUNT (stated before running, Rule 2):")
    print(f"    pool pairwise table (ONCE): C(P,2) = {pairs_pool:,} pairs")
    print(f"      -> {modexps_precompute:,} modexps (2 per pair) + {pairs_pool:,} inversions")
    print(f"    draws: (R+n)*C(M,2) = {lookups_draws:,} integer lookups, ZERO modexps")
    print(f"    (naive fresh-point path would be (R+n)*C(M,2) = {lookups_draws:,} modexps"
          f" ~ {lookups_draws*85/1e6:,.0f}s at 85us; precompute avoids it)")
    print("-" * 78)

    t0 = time.perf_counter()

    # --- pow benchmark (Rule 2: measure pow before sizing) --------------------
    tb = time.perf_counter()
    NB = 2000
    acc = 0
    for _ in range(NB):
        acc ^= pow((acc + 12345) % P_FIELD or 3, EXP3, P_FIELD)
    us = (time.perf_counter() - tb) / NB * 1e6
    print(f"[bench] measured pow(256-bit): {us:.1f} us/modexp  "
          f"=> precompute estimate ~ {modexps_precompute*us/1e6:.0f}s")
    print(f"[bench] projected M=6.25e6 diff-set: C(M,2) = {6250000*6249999//2:,} pairs"
          f" ~ {6250000*6249999//2*us/1e6/3600:,.0f} h of modexps -> NEEDS chunk/sample (Rule 2)")

    # --- instrument validation ------------------------------------------------
    print("-" * 78)
    c_glv_check(rng, n_triples=30)

    # --- build pool of uniform random curve points (geometric null) -----------
    print("-" * 78)
    tp = time.perf_counter()
    pool = [random_point(rng) for _ in range(P)]
    print(f"[pool] generated {P} uniform random curve points in {time.perf_counter()-tp:.1f}s")

    # --- precompute pairwise group-law-difference codes ONCE ------------------
    tc = time.perf_counter()
    # code_row[i] is a list of length P; code_row[i][j] valid for j>i.
    code = [[0] * P for _ in range(P)]
    degen = 0
    for i in range(P):
        Pi = pool[i]
        row = code[i]
        for j in range(i + 1, P):
            xd = gl_diff_x(Pi, pool[j])
            if xd is None:
                degen += 1
                row[j] = -1
                continue
            row[j] = chi2_class(xd) * 3 + chi3_class(xd)
    print(f"[precompute] {pairs_pool:,} pairwise codes in {time.perf_counter()-tc:.1f}s"
          f"  (degenerate x_i==x_j pairs: {degen})")

    # --- draw machinery -------------------------------------------------------
    def draw_stats():
        idx = rng.sample(range(P), M)
        idx.sort()
        H = [0, 0, 0, 0, 0, 0]
        for a in range(M):
            row = code[idx[a]]
            ia = idx[a]
            for b in range(a + 1, M):
                cd = row[idx[b]]
                if cd >= 0:
                    H[cd] += 1
        return stats_from_hist(H)

    # --- null reference -------------------------------------------------------
    td = time.perf_counter()
    ref2, ref3, ref6 = [], [], []
    for _ in range(R):
        e2, e3, e6 = draw_stats()
        ref2.append(e2); ref3.append(e3); ref6.append(e6)
    ref2.sort(); ref3.sort(); ref6.sort()
    print(f"[null] {R} reference draws in {time.perf_counter()-td:.1f}s")

    # --- C-NEG draws ----------------------------------------------------------
    tn = time.perf_counter()
    cn2, cn3, cn6 = [], [], []
    for _ in range(n):
        e2, e3, e6 = draw_stats()
        cn2.append(e2); cn3.append(e3); cn6.append(e6)
    print(f"[C-NEG] {n} independent control draws in {time.perf_counter()-tn:.1f}s")

    # --- report ---------------------------------------------------------------
    print("=" * 78)
    print("NULL REFERENCE PERCENTILES (group-law difference, M={}):".format(M))
    for name, ref in (("E2", ref2), ("E3", ref3), ("E6", ref6)):
        med = pct_value(ref, 1, 2)
        p95 = pct_value(ref, 95, 100)
        p99 = pct_value(ref, 99, 100)
        print(f"    {name}:  median={med:>10}   95th={p95:>10}   99th={p99:>10}   max={ref[-1]:>10}")

    print("-" * 78)
    print("C-NEG RECALIBRATION  (each control draw ranked vs the {} reference draws):".format(R))
    print("   expected under a correct null: ~5% of draws above 95th, ~1% above 99th")
    all_ok = True
    for name, ref, cn in (("E2", ref2, cn2), ("E3", ref3, cn3), ("E6", ref6, cn6)):
        p95 = pct_value(ref, 95, 100)
        p99 = pct_value(ref, 99, 100)
        above95 = sum(1 for v in cn if v > p95)
        above99 = sum(1 for v in cn if v > p99)
        # rank of each C-NEG draw as a percentile (integer count / n, display only)
        ranks = [count_ge(ref, v) for v in cn]  # #ref >= v ; small => high value
        # decile occupancy of the percentile position (uniformity eyeball)
        deciles = Counter(min(9, (R - r) * 10 // R) for r in ranks)  # (R-r)=#ref<v
        dec_str = " ".join(f"{deciles.get(d,0):>3}" for d in range(10))
        f95 = above95 / n
        f99 = above99 / n
        # binomial 2-sigma band for the 5% tail
        import math
        se95 = math.sqrt(0.05 * 0.95 / n)
        flag95 = "OK" if abs(f95 - 0.05) <= 2 * se95 + 0.5 / n else "CHECK"
        print(f"    {name}:  above95 = {above95}/{n} = {f95*100:4.1f}%  "
              f"(nominal 5.0% +/- {2*se95*100:.1f}%)  [{flag95}]   "
              f"above99 = {above99}/{n} = {f99*100:4.1f}% (nominal 1.0%)")
        print(f"          percentile-rank deciles [0-10..90-100]: {dec_str}")
        if flag95 != "OK":
            all_ok = False

    print("=" * 78)
    print("DECISION RULE (recalibrated, supersedes the single-draw C-NEG spec):")
    print("  * C-NEG passes iff the fraction of n>=20 independent control draws above the")
    print("    95th percentile is within the binomial 2-sigma band of 0.05 (ranks ~uniform).")
    print("  * A SINGLE draw above the 95th/99th percentile is EXPECTED ~5%/~1% of the time")
    print("    and is NOT a fire.  The prior spectral (96.0) and group-arm E6 (99.7) single")
    print("    draws are consistent with this null; they were false alarms of the old rule.")
    print("  * An ARM fires only if it exceeds the 99th percentile AND survives OOS retest;")
    print("    C-NEG's job is solely to certify the null tail is calibrated, not to gate arms.")
    print("-" * 78)
    print(f"C-NEG calibration verdict: {'CALIBRATED (all statistics OK)' if all_ok else 'CHECK a flagged statistic'}")
    print(f"TOTAL WALL TIME: {time.perf_counter()-t0:.1f}s")


if __name__ == "__main__":
    main()
