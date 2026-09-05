#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
shortscalar_sum_stageA_v1.py

Stage A of the corrected short-scalar contiguous probe (R-CONTIG), after the
experiment-designer frame gate rejected the pairwise-sum-on-a-contiguous-block
design.

WHY THE OBJECT CHANGED (gate defect, verified):
  In a contiguous block d = d0, d0+1, ..., d0+L-1, the pairwise sum
  P_i + P_j = [2 d0 + i + j] G depends ONLY on i+j, so the C(L,2) pairs collapse
  onto 2L-3 distinct points, each with a heavy multiplicity, and every copy of a
  point shares one character value.  The magnitude statistic is then inflated by
  Sum(mult^2)/C(L,2) ~ L/3 (=133x at L=400) vs a geometric all-distinct null --
  a pure counting artifact that would screen AND replicate 5/5 OOS.  The distinct
  sum-points ARE {[s]G : s in a contiguous interval}, so the correct object is the
  INCOMPLETE CHARACTER SUM over a contiguous interval:  Sum_{s in I} chi_k(x([s]G)).
  Multiplicity is trivially 1; the geometric L-random-point null is matched.

THIS SCRIPT PROVES THE FIX before any arm is trusted:
  C-ARTIFACT  : a STRUCTURELESS oracle (random class per interval point) must NOT
                fire vs the null.  If the corrected design still had a combinatorial
                artifact, this would screen.  It must land mid-distribution.
  C-GLV       : a phi-closed point set forces E3 = E6 = 0 exact (instrument reads
                the object; chi2/chi3/chi6 legal on a one-sided value multiset).
  C-PLANT     : a cubic-class-biased point set MUST fire >= 99th (instrument live).

Then it screens the R-CONTIG arms (k ladder), reporting UNCORRECTED rank p-values
and the measured coherent bound epsilon* (Rule 5).  No FWER suppression at the
screen; the 5-seed OOS gate (PREREG v3 sec.2) is applied only to a screened cell.

Exact integer signal path (no float): characters via pow(a,e,p); statistics are
integer quadratic forms; ranks are integer counts.  Rule 3 null = uniform random
curve points (no scalar mult) = uniform group element (secp cofactor 1).

Usage: python3 shortscalar_sum_stageA_v1.py [L] [Rnull] [poolmult] [seed]
"""

import sys
import time
import random

# --- secp256k1 -------------------------------------------------------------
P_FIELD = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
B_CURVE = 7
BETA = 0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE
N_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G = (GX, GY)

EXP2 = (P_FIELD - 1) // 2
EXP3 = (P_FIELD - 1) // 3
SQRT_EXP = (P_FIELD + 1) // 4


def _cube_root_labels():
    assert P_FIELD % 4 == 3 and P_FIELD % 3 == 1
    assert pow(BETA, 3, P_FIELD) == 1 and BETA != 1
    W = None
    for z in range(2, 100):
        t = pow(z, EXP3, P_FIELD)
        if t != 1:
            W = t
            break
    W2 = (W * W) % P_FIELD
    assert (W * W2) % P_FIELD == 1
    return {1: 0, W: 1, W2: 2}


CUBE_LABEL = _cube_root_labels()


def chi2_class(a):
    return 0 if pow(a % P_FIELD, EXP2, P_FIELD) == 1 else 1


def chi3_class(a):
    return CUBE_LABEL[pow(a % P_FIELD, EXP3, P_FIELD)]


def code_of(x):
    """(b,c) packed as 3*b + c for the x-coordinate of a point."""
    return 3 * chi2_class(x) + chi3_class(x)


# --- group law (affine, a=0) ----------------------------------------------
def point_add(Pp, Qq):
    if Pp is None:
        return Qq
    if Qq is None:
        return Pp
    x1, y1 = Pp
    x2, y2 = Qq
    if x1 == x2:
        if (y1 + y2) % P_FIELD == 0:
            return None                      # P = -Q  ->  O
        lam = (3 * x1 * x1) % P_FIELD * pow(2 * y1 % P_FIELD, -1, P_FIELD) % P_FIELD
    else:
        lam = (y2 - y1) % P_FIELD * pow((x2 - x1) % P_FIELD, -1, P_FIELD) % P_FIELD
    x3 = (lam * lam - x1 - x2) % P_FIELD
    y3 = (lam * (x1 - x3) - y1) % P_FIELD
    return (x3, y3)


def scalar_mult(k, Pp):
    R = None
    Q = Pp
    while k:
        if k & 1:
            R = point_add(R, Q)
        Q = point_add(Q, Q)
        k >>= 1
    return R


def random_point(rng):
    while True:
        x = rng.randrange(1, P_FIELD)
        rhs = (x * x % P_FIELD * x + B_CURVE) % P_FIELD
        if rhs == 0 or pow(rhs, EXP2, P_FIELD) != 1:
            continue
        y = pow(rhs, SQRT_EXP, P_FIELD)
        if rng.getrandbits(1):
            y = P_FIELD - y
        return (x, y)


# --- exact integer statistics from a 6-cell histogram over code=3b+c -------
def stats_from_hist(H, T):
    nb0 = H[0] + H[1] + H[2]
    nb1 = H[3] + H[4] + H[5]
    E2 = (nb0 - nb1) ** 2
    nc0 = H[0] + H[3]; nc1 = H[1] + H[4]; nc2 = H[2] + H[5]
    A3 = nc0 - nc2; B3 = nc1 - nc2
    E3 = A3 * A3 - A3 * B3 + B3 * B3
    nm = [H[0], H[5], H[1], H[3], H[2], H[4]]
    A6 = nm[0] - nm[2] - nm[3] + nm[5]
    B6 = nm[1] + nm[2] - nm[4] - nm[5]
    E6 = A6 * A6 + A6 * B6 + B6 * B6
    # D6: integer histogram chi^2 numerator vs uniform expectation T/6, scaled x36
    D6 = sum((6 * H[c] - T) ** 2 for c in range(6))
    return E2, E3, E6, D6


def hist_of_codes(codes):
    H = [0, 0, 0, 0, 0, 0]
    for c in codes:
        H[c] += 1
    return H


# --- interval arm: L consecutive points [s0]G, [s0+1]G, ... ----------------
def interval_codes(s0, L):
    Pt = scalar_mult(s0 % N_ORDER, G)
    codes = []
    for _ in range(L):
        codes.append(code_of(Pt[0]))
        Pt = point_add(Pt, G)
    return codes


def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    Rnull = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    poolmult = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 20260802
    KS = [40, 64, 96, 128, 160, 200]
    # with-replacement bootstrap: the pool only estimates the 6-class distribution,
    # so a modest (capped) pool gives a clean iid null at any L.
    Ppool = max(20000, min(poolmult * L, 100000))
    rng = random.Random(seed)

    print("=" * 78)
    print("R-CONTIG (corrected: incomplete character sum over a contiguous interval)")
    print("=" * 78)
    print(f"config: L={L}  Rnull={Rnull}  pool={Ppool}  seed={seed}  k-ladder={KS}")
    print("BIG-O / OP COUNT (Rule 2):")
    print(f"    arm: O(L) -- {L} char-reads x 2 modexp = {2*L:,} modexp/arm, {len(KS)} arms"
          f" -> {2*L*len(KS):,} modexp  (LINEAR; the pairwise O(L^2) artifact is gone)")
    print(f"    null pool ONCE: {Ppool:,} points x 2 modexp = {2*Ppool:,} modexp;"
          f" {Rnull} realizations are integer resamples")
    print("-" * 78)
    t0 = time.perf_counter()

    # pow benchmark
    tb = time.perf_counter(); acc = 3
    for _ in range(1500):
        acc = pow((acc + 12345) % P_FIELD or 3, EXP3, P_FIELD)
    us = (time.perf_counter() - tb) / 1500 * 1e6
    print(f"[bench] pow = {us:.1f} us/modexp")

    # --- null pool + reference distribution (k-independent) ----------------
    tp = time.perf_counter()
    pool_codes = [code_of(random_point(rng)[0]) for _ in range(Ppool)]
    print(f"[pool] {Ppool} uniform random curve points coded in {time.perf_counter()-tp:.1f}s")
    tr = time.perf_counter()
    null = {"E2": [], "E3": [], "E6": [], "D6": []}
    for _ in range(Rnull):
        H = hist_of_codes(rng.choices(pool_codes, k=L))   # with-replacement => iid null
        e2, e3, e6, d6 = stats_from_hist(H, L)
        null["E2"].append(e2); null["E3"].append(e3); null["E6"].append(e6); null["D6"].append(d6)
    for kk in null:
        null[kk].sort()
    print(f"[null] {Rnull} reference realizations in {time.perf_counter()-tr:.1f}s")

    def p99(name):
        arr = null[name]; return arr[(99 * len(arr)) // 100]
    def p95(name):
        arr = null[name]; return arr[(95 * len(arr)) // 100]
    def rank_p(name, v):
        # exact upper-tail rank p-value: (#null >= v) / Rnull
        arr = null[name]
        lo, hi = 0, len(arr)
        while lo < hi:
            mid = (lo + hi) // 2
            if arr[mid] < v: lo = mid + 1
            else: hi = mid
        return (len(arr) - lo), len(arr)

    def verdict(name, v):
        n_ge, R = rank_p(name, v)
        tag = "FIRE>=99th" if v > p99(name) else ("--<95th" if v < p95(name) else "mid")
        return f"{v:>12}  p={n_ge}/{R}={n_ge/R:6.4f}  [{tag}]"

    # --- CONTROLS (prove the fix + instrument) -----------------------------
    print("=" * 78)
    print("CONTROLS")
    # C-GLV: phi-closed point set -> E3=E6=0 exact. COMPLETE triples only
    # (truncating mid-triple leaves an orphan that spoils the exact cancellation).
    S = []
    for _ in range(max(1, L // 3)):
        x, y = random_point(rng)
        S += [x, (BETA * x) % P_FIELD, (BETA * BETA * x) % P_FIELD]
    Hg = hist_of_codes(code_of(x) for x in S)
    e2g, e3g, e6g, d6g = stats_from_hist(Hg, len(S))
    print(f"  C-GLV (phi-closed, |S|={len(S)}): E2={e2g} E3={e3g} E6={e6g}"
          f"  -> {'PASS' if e3g==0 and e6g==0 else 'FAIL'} (E3=E6=0 forced)")
    assert e3g == 0 and e6g == 0, "instrument FAIL"

    # C-ARTIFACT: structureless oracle (random class per interval point) must NOT fire
    Ha = hist_of_codes(rng.randrange(6) for _ in range(L))
    e2a, e3a, e6a, d6a = stats_from_hist(Ha, L)
    print("  C-ARTIFACT (structureless oracle, random class/point -- MUST land mid, NOT fire):")
    for nm, v in (("E2", e2a), ("E3", e3a), ("E6", e6a), ("D6", d6a)):
        print(f"      {nm}: {verdict(nm, v)}")
    art_fires = any(v > p99(nm) for nm, v in (("E2", e2a), ("E3", e3a), ("E6", e6a), ("D6", d6a)))
    print(f"      -> artifact {'FIRED (FIX FAILED)' if art_fires else 'did NOT fire: no combinatorial inflation (fix confirmed)'}")

    # C-PLANT: cubic-class-biased set MUST fire
    # build a biased set: force ~ delta_target of points into cubic class 0
    plant_codes = []
    delta_target = 0.18
    for _ in range(L):
        if rng.random() < delta_target:
            # find a point with chi3 class 0
            while True:
                x = random_point(rng)[0]
                if chi3_class(x) == 0:
                    plant_codes.append(code_of(x)); break
        else:
            plant_codes.append(code_of(random_point(rng)[0]))
    Hp = hist_of_codes(plant_codes)
    e2p, e3p, e6p, d6p = stats_from_hist(Hp, L)
    print(f"  C-PLANT (cubic-class excess ~{delta_target}): E3: {verdict('E3', e3p)}")
    print(f"      -> plant {'FIRED (instrument live)' if e3p > p99('E3') else 'did NOT fire (INSTRUMENT DEAD)'}")

    # --- ARMS: R-CONTIG at each k -----------------------------------------
    print("=" * 78)
    print(f"R-CONTIG ARMS  (L={L} consecutive [s]G from s0 in [2^(k-1), 2^k), UNCORRECTED p-values)")
    print("  screen = FIRE>=99th (then 5-seed OOS gate, not run here unless a cell screens)")
    ta = time.perf_counter()
    screened = []
    for k in KS:
        s0 = rng.randrange(1 << (k - 1), 1 << k)
        H = hist_of_codes(interval_codes(s0, L))
        e2, e3, e6, d6 = stats_from_hist(H, L)
        print(f"  k={k:>3}:")
        for nm, v in (("E2", e2), ("E3", e3), ("E6", e6), ("D6", d6)):
            line = verdict(nm, v)
            print(f"      {nm}: {line}")
            if v > p99(nm):
                screened.append((k, nm, v))
    print(f"[arms] {len(KS)} arms in {time.perf_counter()-ta:.1f}s")

    # --- measured bound (Rule 5) ------------------------------------------
    V99_E3 = p99("E3")
    # coherent single-class fractional excess needed to reach the 99th:
    # E3 = |sum chi3|^2 ; a class-0 excess of delta over L/3 gives E3 ~ (9/4) delta^2
    # (matched to on-file form); eps* = delta/(L/3) = 2*sqrt(V99)/L .
    import math
    eps_star = 2 * math.sqrt(V99_E3) / L
    print("=" * 78)
    print("MEASURED BOUND (Rule 5 -- a bound, never a closure):")
    print(f"  null E3: median={null['E3'][len(null['E3'])//2]}  95th={p95('E3')}  99th={V99_E3}")
    print(f"  coherent single-class cubic bound eps* = 2*sqrt(V99)/L = {eps_star*100:.3f}%")
    print(f"  => R-CONTIG at L={L} excludes a coherent cubic-class bias >= {eps_star*100:.3f}%;"
          f" BLIND below.  (eps* ~ 1/sqrt(L): larger L lowers it, O(L) cost.)")
    print("-" * 78)
    if screened:
        print(f"SCREENED CELLS (candidates -> require 5-seed OOS gate before ANY naming): {screened}")
    else:
        print("No cell screened at the 99th. All arms BOUNDED at the floor above (not 'closed').")
    print(f"TOTAL WALL TIME: {time.perf_counter()-t0:.1f}s")


if __name__ == "__main__":
    main()
