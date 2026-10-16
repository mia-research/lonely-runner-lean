#!/usr/bin/env python3
"""Observation. The finite list: every coprime §6 set with D < 15 lying in a failing cell of s6_rest_v6 (c <= 30):
v2 = cD, v3 = (c+1)D, v4 = v3 + delta, v1 = a (mod D) with v1 < v3/3, v1 < v2, and v5 > v4 with M = v4/(3 v5) >= the cell's
smallest failing M (v5 <= v4/(3 M_min)). For each set (not only primitive): uniform?, region (exact), sum lemma, exact
meeting fold, and else the first lonely instant found by an exact interval scan of [0, 1]."""
import math, ast
from fractions import Fraction as F
from collections import Counter
from s6_rest_v1 import uniform, region_ks, sum_ok, meet_fold
cells = []
for line in open("s6_rest_v6.out"):
    if line.startswith("   ("):
        tup, rng = line.strip().split(" M in ")
        cells.append((ast.literal_eval(tup), ast.literal_eval(rng)))
def lonely_scan(S):
    # clear intervals of each runner in [0,1]; intersect
    iv = [(F(0), F(1))]
    for v in S:
        nv = []
        for m in range(v + 1):
            a, b = F(6 * m + 1, 6 * v), F(6 * m + 5, 6 * v)
            for lo, hi in iv:
                x, y = max(lo, a), min(hi, b)
                if x <= y: nv.append((x, y))
        iv = nv
        if not iv: return None
    return min(iv)
res = Counter(); rest = []; n = 0
for (D, c, d, a, lam), (mlo, mhi) in cells:
    v2, v3 = c * D, (c + 1) * D; v4 = v3 + d
    for v1 in range(a, min(v2, (v3 + 2) // 3), D):
        if 3 * v1 >= v3: continue
        v5 = v4 + 1
        while F(v4, 3 * v5) >= F(mlo) - F(1, 720):
            S = (v1, v2, v3, v4, v5); n += 1
            how = ("uniform" if uniform(S) else "region" if region_ks(S, range(D)) is not None else
                   "sum" if sum_ok(S) else "meeting fold" if meet_fold(S) else "other")
            res[how] += 1
            if how == "other": rest.append((S, lonely_scan(S)))
            v5 += 1
print(f"sets in the failing cells (c <= 30): {n}: {dict(res)}")
for S, t in rest: print("  not closed by the four windows:", S, "first lonely interval", t)
