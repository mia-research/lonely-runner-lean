#!/usr/bin/env python3
"""Observation: §6 sets where s6_meeting_uniform's condition fails (runner 4 close to runner 3). Test the meeting-window
four-block fold: for some k (1 <= k <= 2D) and side (after / before the meeting time k/D), runners 2, 3 clear on J_k;
runners 1 and 4 clear on a common sub-window W of J_k (any laps); runner 5 folded alone (v5 |W| >= 1/3).
Recorded per set: whether it closes; the k used; and the phases (k v1 mod D, k delta mod D)/D, delta = v4 - v3,
of the successful k (to see the 2D-orbit picture)."""
import math, sys, random
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
def s6(S):
    v1, v2, v3 = S[:3]; D = v3 - v2
    return v3 > 3 * v1 and v3 % D == 0 and v1 % D != 0
def uniform(S): v1, v2, v3, v4, v5 = S; return 4 * v2 * v3 <= v4 * (5 * v2 - v3)
def clear_sub(v, L, U):
    out = []
    for m in range(int(L * v) - 1, int(U * v) + 2):
        a = max(L, F(6 * m + 1, 6 * v)); b = min(U, F(6 * m + 5, 6 * v))
        if a <= b: out.append((a, b))
    return out
def meet_fold(S):
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    for k in range(1, 2 * D + 1):
        t0 = F(k, D)
        for L, U in ((t0 + F(1, 6 * v2), t0 + F(5, 6 * v3)), (t0 - F(5, 6 * v3), t0 - F(1, 6 * v2))):
            for a1, b1 in clear_sub(v1, L, U):
                for a4, b4 in clear_sub(v4, a1, b1):
                    if v5 * (b4 - a4) >= F(1, 3):
                        return k, (F(k * v1 % D, D), F(k * (v4 - v3) % D, D))
    return None
H = int(sys.argv[1]) if len(sys.argv) > 1 else 34
sets = [S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and s6(S) and not uniform(S)]
random.seed(7)
while len(sets) < len(sets) + 0 and False: pass
res = Counter(); ph = Counter(); miss = []
for S in sets:
    r = meet_fold(S)
    if r: res["closed"] += 1; ph[(int(6 * r[1][0]), int(6 * r[1][1]))] += 1
    else: res["not"] += 1; miss.append(S)
print(f"§6 <= {H}, uniform condition fails: {len(sets)}; meeting-window four-block fold: {dict(res)}; not closed {miss[:12]}")
print("successful k: (sixth of k v1 mod D, sixth of k delta mod D):", ph.most_common(12))
