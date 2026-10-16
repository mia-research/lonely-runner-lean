#!/usr/bin/env python3
"""Neighbours of the second tight set (1,2,3,4,5) inside §5 k = 1: v = (c, 2c + d2, 3c + d2, 4c + d4, 5c + d5) with d2 >= 1
(3 v1 < v3 forces it). At T = v1 t = 1/6 the tight readings are (1/6, 1/3, 1/2, 2/3, 5/6): runners 1 and 5 on band edges.
Grouped by the sign of d5 (runner 5 vs 5 v1) and d4: lonely or not, the earliest lonely T and window length (in T), and for
d5 = 0 the product a T (a = d2/c) to test drift."""
import math
from collections import defaultdict
from s5k1_tight_v2 import lonely
g = defaultdict(list)
for c in range(6, 61):
    for d2 in range(1, 4):
        for d4 in range(-3, 4):
            for d5 in range(-3, 4):
                S = (c, 2 * c + d2, 3 * c + d2, 4 * c + d4, 5 * c + d5)
                if not all(S[i] < S[i + 1] for i in range(4)) or math.gcd(*S) != 1: continue
                key = ("d5<0" if d5 < 0 else "d5>0" if d5 > 0 else "d5=0") + (", d4=0" if d4 == 0 else ", d4!=0")
                iv = lonely(S)
                g[key].append((S, round(iv[0][0] * c, 4) if iv else None, round((iv[0][1] - iv[0][0]) * c, 5) if iv else None))
for key in sorted(g):
    l = g[key]
    starts = sorted(set(x[1] for x in l if x[1] is not None))
    print(f"{key}: {len(l)} sets; not lonely: {[x[0] for x in l if x[1] is None][:5]}; earliest T: {starts[:6]} ... max {starts[-1] if starts else None}")
    if key.startswith("d5=0"):
        for x in sorted(l, key=lambda x: -x[0][0])[:6]:
            a = (x[0][1] - 2 * x[0][0]) / x[0][0]
            print(f"     {x[0]}  a = {a:.4f}  T = {x[1]}  a*T = {a * x[1] if x[1] else None}")
