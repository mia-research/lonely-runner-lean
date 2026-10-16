#!/usr/bin/env python3
"""Observation: §6 sets with v4 = v3 + v1 (the lam = 1 family that misses the E94 region), primitive <= 60, not uniform.
For each meeting time k/D (k = 1..D) and both windows: does the exact fold work (runners 2, 3 clear; runners 1 and 4 clear
on a common sub-window; runner 5 folded)? Record the runner-1 phase p1 = (k v1 mod D)/D of the working k, in 36ths."""
import math
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("s6_near_v1.py").read().split("H = int(")[0])
def fold_side(S, k, after):
    v1, v2, v3, v4, v5 = S; D = v3 - v2; t0 = F(k, D)
    L, U = (t0 + F(1, 6 * v2), t0 + F(5, 6 * v3)) if after else (t0 - F(5, 6 * v3), t0 - F(1, 6 * v2))
    return any(v5 * (b4 - a4) >= F(1, 3) for a1, b1 in clear_sub(v1, L, U) for a4, b4 in clear_sub(v4, a1, b1))
work = Counter(); n = 0; byc = Counter()
for S in combinations(range(1, 61), 5):
    if math.gcd(*S) != 1 or not s6(S) or uniform(S): continue
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    if v4 != v3 + v1: continue
    n += 1; byc[v3 // D - 1] += 1
    for k in range(1, D + 1):
        p = F(k * v1 % D, D)
        if fold_side(S, k, True): work[("after", int(36 * p))] += 1
        if fold_side(S, k, False): work[("before", int(36 * p))] += 1
print(f"v4 = v3 + v1 sets (not uniform) <= 60: {n}; by c: {dict(sorted(byc.items()))}")
for side in ("after", "before"):
    print(side, "working p1 (36ths : count):", sorted((b, c) for (s, b), c in work.items() if s == side))
