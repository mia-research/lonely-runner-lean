#!/usr/bin/env python3
"""Observation: the near-runner §6 sets as a 2D orbit. Phases at the meeting time k/D: p1 = (k v1 mod D)/D (runner 1),
p4 = (k delta mod D)/D (runner 4, delta = v4 - v3). Candidate box B = [1/6, 5/9] x [0, b] for b in {1/12, 1/6, 1/4}:
(a) does the orbit k -> (p1, p4), k = 1..D, always meet B?  (b) whenever (p1, p4) is in B, does the after-window fold
close the set (runner 1 and 4 clear on a common sub-window of J+_k of length >= 1/(3 v5))?"""
import math, sys
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("s6_near_v1.py").read().split("H = int(")[0])
def fold_at(S, k):
    v1, v2, v3, v4, v5 = S; D = v3 - v2; t0 = F(k, D)
    L, U = t0 + F(1, 6 * v2), t0 + F(5, 6 * v3)
    return any(v5 * (b4 - a4) >= F(1, 3) for a1, b1 in clear_sub(v1, L, U) for a4, b4 in clear_sub(v4, a1, b1))
H = int(sys.argv[1]) if len(sys.argv) > 1 else 34
sets = [S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and s6(S) and not uniform(S)]
for b in (F(1, 12), F(1, 6), F(1, 4)):
    meet = 0; good = Counter(); misses = []
    for S in sets:
        v1, v2, v3, v4, v5 = S; D = v3 - v2; d = v4 - v3
        ks = [k for k in range(1, D + 1) if F(1, 6) <= F(k * v1 % D, D) <= F(5, 9) and F(k * d % D, D) <= b]
        if ks: meet += 1
        else: misses.append(S)
        for k in ks: good[fold_at(S, k)] += 1
    print(f"box [1/6,5/9] x [0,{b}]: orbit meets it in {meet}/{len(sets)} sets (misses {misses[:6]}); fold closes at the box's k: {dict(good)}")
