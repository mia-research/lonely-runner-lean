#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
n15_threepoint_tuple_filter_v1.py — the 3-point tuple closure: MI(t(s); (t1,t2,t3)) over triples,
s = d1+d2+d3, with the shuffled-tuple null — same design as the 2-point closure, one rung up.
Excludes the forced vanishing loci (any sub-sum or the total = 0 mod n). Exact enumeration.
"""
import math, random, sys, os
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import enorm
from m40_n15_exact_accounting_v1 import curve_walk

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

def mi3(t, n):
    cj = Counter(); cS = Counter(); cT = Counter(); N = 0
    for d1 in range(1, n):
        t1 = t[d1]
        for d2 in range(1, n):
            s12 = d1 + d2
            if s12 % n == 0:
                continue
            t2 = t[d2]
            for d3 in range(1, n):
                s = (s12 + d3) % n
                if s == 0 or d1 == d3 or d2 == d3:
                    continue
                t3 = t[d3]; ts = t[s]
                cj[(ts, t1, t2, t3)] += 1; cS[ts] += 1; cT[(t1, t2, t3)] += 1; N += 1
    return sum(c / N * math.log2((c * N) / (cS[ts] * cT[(t1, t2, t3)]))
               for (ts, t1, t2, t3), c in cj.items())

print("=" * 100)
print(" 3-POINT TUPLE MI — real vs shuffled null, off forced vanishing loci (exact enumeration)")
print("=" * 100)
print(f" {'p':>4} {'n':>4} | {'MI3':>9} {'null mean':>10} {'null sd':>8} {'z':>7} | {'(MI-null)*n':>11}")
for p in (43, 79, 163, 211):
    n, h, xs = curve_walk(p)
    eisp, epsp = build(p)
    tup = [None] * n
    for d in range(1, n):
        tup[d] = tuple_of(eisp, epsp, xs[d], p) + (h[d],)
    MI = mi3(tup, n)
    random.seed(20260823)
    NDRAWS = 100 if n < 50 else (12 if n < 150 else 3)
    nulls = []
    for _ in range(NDRAWS):
        perm = list(range(1, n))
        random.shuffle(perm)
        nulls.append(mi3([tup[perm[d - 1]] if d else None for d in range(n)], n))
    mu = sum(nulls) / len(nulls)
    sd = (sum((x - mu) ** 2 for x in nulls) / len(nulls)) ** 0.5
    z = (MI - mu) / sd if sd else float("inf")
    print(f" {p:>4} {n:>4} | {MI:9.5f} {mu:10.5f} {sd:8.5f} {z:7.2f} | {(MI - mu) * n:11.2f}", flush=True)
print("=" * 100)
