#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
n15_twopoint_tuple_scaling_v2.py — decide the two-point tuple MI: finite-size artifact or structure?
Adds (a) the SHUFFLED-TUPLE NULL (random relabeling of tuples over d — same cell-size structure,
destroyed d-assignment; 200 draws) and (b) a wide prime sweep n up to ~2700.

Reads:
  MI ~ c/n (or null-consistent)  => finite-size / Weil-scale; the two-point tuple door closes at secp
  MI ~ c > null at large n        => REAL two-point tuple structure — a live N15 lead
"""
import math, random, sys, os
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from int1_frame_operator_v1 import build
from m40_n15_exact_accounting_v1 import curve_walk

def tuple_of(eisp, epsp, X, p):
    from lift_sextant_rhombus_law_proof_v2 import enorm
    u, v = eisp(X)
    e = epsp(X)
    s = enorm((u, v))
    band = 0 if 16 * s < 3 * p else (1 if 4 * s < p else 2)
    a1, a2, a3 = u, v, u - v
    if a1 >= 0 and a2 >= 0: sext = 0
    elif a1 >= 0 and a3 >= 0: sext = 1
    elif a3 >= 0 and a2 < 0: sext = 2
    elif a1 < 0 and a2 < 0: sext = 3
    elif a1 < 0 and a3 < 0: sext = 4
    else: sext = 5
    return (e, sext, band)

def mi_pairs(tup, n, d_perm=None):
    """MI(t12; (t1,t2)) over all pairs with d1+d2 != 0. d_perm: optional relabeling of d's."""
    t = tup if d_perm is None else [tup[d_perm[d]] for d in range(n)]
    cj = Counter(); cA = Counter(); cB = Counter(); N = 0
    for d1 in range(1, n):
        t1 = t[d1]
        for d2 in range(1, n):
            if (d1 + d2) % n == 0:
                continue
            t2 = t[d2]; t12 = t[(d1 + d2) % n]
            cj[(t12, t1, t2)] += 1; cA[t12] += 1; cB[(t1, t2)] += 1; N += 1
    return sum(c / N * math.log2((c * N) / (cA[t12] * cB[(t1, t2)]))
               for (t12, t1, t2), c in cj.items())

print("=" * 104)
print(" TWO-POINT TUPLE MI — real vs shuffled-null, wide n sweep (exact enumeration per prime)")
print("=" * 104)
print(f" {'p':>5} {'n':>5} | {'MI':>9} {'null mean':>10} {'null sd':>8} {'z':>8} | {'MI*n':>7} {'MI*sqrt(n)':>10}")
for p in (43, 79, 163, 211, 547, 823, 1051, 1303, 1831):
    n, h, xs = curve_walk(p)
    eisp, epsp = build(p)
    tup = [None] * n
    for d in range(1, n):
        tup[d] = tuple_of(eisp, epsp, xs[d], p) + (h[d],)
    MI = mi_pairs(tup, n)
    random.seed(20260822)
    perm = list(range(1, n))
    NDRAWS = 200 if n < 300 else (40 if n < 1200 else 12)
    nulls = []
    for _ in range(NDRAWS):
        random.shuffle(perm)
        dp = [0] + perm            # relabel d -> permuted d (identity at 0; O unused)
        nulls.append(mi_pairs(tup, n, d_perm=dp))
    mu = sum(nulls) / len(nulls)
    sd = (sum((x - mu) ** 2 for x in nulls) / len(nulls)) ** 0.5
    z = (MI - mu) / sd if sd else float('inf')
    print(f" {p:>5} {n:>5} | {MI:9.5f} {mu:10.5f} {sd:8.5f} {z:8.2f} | {MI*n:7.1f} {MI*math.sqrt(n):10.3f}",
          flush=True)
print("=" * 104)
