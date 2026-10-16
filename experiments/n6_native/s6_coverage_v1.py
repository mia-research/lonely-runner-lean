#!/usr/bin/env python3
"""§6 coverage by the proved meeting-window theorem (s6_meeting_uniform: 4 v2 v3 <= v4 (5 v2 - v3)), on all primitive
§6 sets <= H and random §6 sets <= 1000; for the rest: closed by the meeting window with window_two's sharp conditions
(any k <= 2D, after/before, on runner 1's clear sub-windows), else by a four-block fold (any laps, t <= 3/v1), else
listed; plus the ratio (v4 - v3)/D on the rest."""
import math, sys, random
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("s56_families_v1.py").read().split("def run(")[0])
def s6(S):
    v1, v2, v3 = S[:3]; D = v3 - v2
    return v3 > 3 * v1 and v3 % D == 0 and v1 % D != 0
def uniform(S):
    v1, v2, v3, v4, v5 = S
    return 4 * v2 * v3 <= v4 * (5 * v2 - v3)
def run(sets, label):
    c = Counter(); rest = []; gap = Counter()
    for S in sets:
        if uniform(S): c["uniform (proved)"] += 1
        elif fam(S): c["meeting window, sharp"] += 1
        elif fold(S): c["four-block fold"] += 1
        else: c["rest"] += 1; rest.append(S)
        if not uniform(S): gap[round(float(F(S[3] - S[2], S[2] - S[1])), 1)] += 1
    print(f"{label}: {len(sets)} §6 sets: {dict(c)}; rest {rest[:10]}")
    print("   (v4 - v3)/D where the uniform condition fails:", sorted(gap.items())[:12])
H = int(sys.argv[1]) if len(sys.argv) > 1 else 36
run([S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and s6(S)], f"§6 <= {H}")
random.seed(6); big = []
while len(big) < 2000:
    S = tuple(sorted(random.sample(range(1, 1001), 5)))
    if math.gcd(*S) == 1 and s6(S): big.append(S)
run(big, "random §6 <= 1000")
