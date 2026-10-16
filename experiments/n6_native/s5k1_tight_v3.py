#!/usr/bin/env python3
"""Neighbours v = (c, 3c + d2, 4c + d2, 5c + d4, 9c + d5) of the tight set. Besides v3 = v1 + v2 (k = 1), the tight set
satisfies three relations: v2 = 3 v1 (broken by d2), v4 = 5 v1 (broken by d4), v5 = v3 + v4 (broken by e5 = d5 - d2 - d4).
Per neighbour: which relations are broken, and the earliest lonely interval in units T = c t (start, length*c).
Grouped by the pattern of broken relations (and sign of d4)."""
import math
from collections import defaultdict
from s5k1_tight_v2 import lonely
g = defaultdict(list)
for c in range(6, 41):
    for d2 in range(-3, 4):
        for d4 in range(-3, 4):
            for d5 in range(-5, 6):
                S = (c, 3 * c + d2, 4 * c + d2, 5 * c + d4, 9 * c + d5)
                if (d2, d4, d5) == (0, 0, 0) or not all(S[i] < S[i + 1] for i in range(4)) or math.gcd(*S) != 1: continue
                e5 = d5 - d2 - d4
                key = ("d4<0" if d4 < 0 else "d4>0" if d4 > 0 else "d4=0") + (", e5=0" if e5 == 0 else ", e5!=0") + (", d2=0" if d2 == 0 else ", d2!=0")
                iv = lonely(S)
                g[key].append((S, round(iv[0][0] * c, 4), round((iv[0][1] - iv[0][0]) * c, 5)) if iv else (S, None, None))
for key in sorted(g):
    l = g[key]
    starts = sorted(set(x[1] for x in l if x[1] is not None))
    print(f"{key}: {len(l)} sets; none lonely: {sum(1 for x in l if x[1] is None)}; earliest start T = c t: min {starts[0] if starts else None}, values {starts[:8]}")
    for x in l[:4]: print("    ", x)
