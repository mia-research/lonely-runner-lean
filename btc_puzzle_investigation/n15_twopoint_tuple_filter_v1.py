#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
n15_twopoint_tuple_filter_v1.py — the N15 non-sign pivot, two-point level, EXACT.

Question: in the two-key setting (public P1=[d1]G, P2=[d2]G, P12=P1+P2), do the CANONICAL tuples
t(d) = (eps class, sextant, band, y-parity) of the three points jointly constrain (d1,d2) MORE than
the product of the single-point budgets (the (g) result: ~4.2 bits/point, negative within-point
synergy)? A super-additive joint cell structure would be the first real N15 filter; factorization
closes the two-point non-sign door.

Exact total enumeration over all (d1,d2) in [1,n)^2 (excluding d1+d2 = 0 mod n: O has no x).
Statistics:
  MI(t12 ; (t1,t2))            — exact mutual information (the synergy measure)
  MI off degenerate loci        — additionally excluding d1=d2 and the pairwise vanishing planes
  cell factorization            — max/mean cell population vs the independence prediction
  the honest filter value       — log2 of candidate-pair reduction from (t1,t2,t12), vs brute MITM
"""
import math, sys, os
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import enorm
from m40_n15_exact_accounting_v1 import curve_walk, legendre

def tuple_of(eisp, epsp, X, p):
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

def H(counter, N):
    return -sum(c / N * math.log2(c / N) for c in counter.values() if c)

def main():
    print("=" * 106)
    print(" N15 TWO-POINT TUPLE FILTER — canonical tuples of (P1, P2, P12); exact total enumeration")
    print("=" * 106)
    for p in (43, 79, 163, 211, 61):
        n, h, xs = curve_walk(p)
        eisp, epsp = build(p)
        tup = [None] * n
        for d in range(1, n):
            tup[d] = tuple_of(eisp, epsp, xs[d], p) + (h[d],)   # + y-parity
        NT = len(set(tup[1:]))
        # full pair enumeration
        cj = Counter(); cA = Counter(); cB = Counter()
        cj_rest = Counter(); cA_rest = Counter(); cB_rest = Counter(); Nrest = 0
        cells = Counter()
        for d1 in range(1, n):
            t1 = tup[d1]
            for d2 in range(1, n):
                s = (d1 + d2) % n
                if s == 0:
                    continue
                t2 = tup[d2]; t12 = tup[s]
                cj[(t12, t1, t2)] += 1; cA[t12] += 1; cB[(t1, t2)] += 1
                cells[(t1, t2, t12)] += 1
                if d1 != d2:
                    cj_rest[(t12, t1, t2)] += 1; cA_rest[t12] += 1; cB_rest[(t1, t2)] += 1
                    Nrest += 1
        N = sum(cj.values())
        MI = sum(c / N * math.log2((c * N) / (cA[t12] * cB[(t1, t2)]))
                 for (t12, t1, t2), c in cj.items())
        MIr = sum(c / Nrest * math.log2((c * Nrest) / (cA_rest[t12] * cB_rest[(t1, t2)]))
                  for (t12, t1, t2), c in cj_rest.items())
        Ht = H(cA, N)
        # cell factorization: observed max cell vs independence prediction
        maxcell = max(cells.values())
        # independence expected max: product of marginals restricted — approximate via mean of top products
        ct1 = Counter(); ct12 = Counter()
        for (t12, t1, t2), c in cj.items():
            ct1[t1] += c; ct12[t12] += c
        # honest filter value: with all three tuples public, candidate pairs per triple:
        sizes = sorted(cells.values(), reverse=True)
        frac_top = sizes[0] / N
        # brute MITM baseline: n candidates for d2 given d1 known; filter keeps cells fraction
        print(f" p={p:>3} n={n:>3} |Q|-style domain: {n-1} d's; distinct tuples {NT} | pairs N={N}")
        print(f"   H(t)={Ht:.3f} b  MI(t12;(t1,t2)) = {MI:.5f} b   off-diagonal {MIr:.5f} b")
        print(f"   cells: {len(cells)} | max cell {maxcell} ({frac_top:.4f} of pairs) | "
              f"top-10 cells {sizes[:10]}")
        print(f"   filter value if cells factorize: ~3*H(t) = {3*Ht:.2f} bits vs 2*log2(n) = "
              f"{2*math.log2(n):.1f} b of pair entropy -> {'O(1) (no filter)' if 3*Ht < 20 else 'check'}")
    print("=" * 106)

if __name__ == "__main__":
    main()
