#!/usr/bin/env python3
"""Check of the derived sum-relation window (v4 = v3 + v1). After the meeting time k/D, on s with v3 s in [7/6 - p, 5/6]
(p = runner 1's phase): runner 3 in band, runner 2 in band (c >= 1), runner 1 reads p + v1 s <= 5/6 when
p <= (5/6)(1 - v1/v3), runner 4 reads v3 s + p + v1 s, which is past a whole lap and in band, and runner 5 is folded when
the window (p - 1/3)/v3 >= 1/(3 v5). So any k with p in I = [1/3 + v3/(3 v5), (5/6)(1 - v1/v3)] works.
Check: (a) on all §6 sets <= 60 with v4 = v3 + v1, the sets where some k has p in I, and that the fold indeed works
at that k (exact); (b) the rest, with their ratios v3/v1 and v5/v4."""
import math
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("s6_sum_v1.py").read().split("work = Counter()")[0])
c = Counter(); rest = []; bad = 0
for S in combinations(range(1, 61), 5):
    if math.gcd(*S) != 1 or not s6(S): continue
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    if v4 != v3 + v1: continue
    lo, hi = F(1, 3) + F(v3, 3 * v5), F(5, 6) * (1 - F(v1, v3))
    ks = [k for k in range(1, D + 1) if lo <= F(k * v1 % D, D) <= hi]
    if ks:
        c["k in I"] += 1
        bad += not fold_side(S, ks[0], True)
    else:
        c["no k in I"] += 1; rest.append((S, round(float(F(v3, v1)), 2), round(float(F(v5, v4)), 2), "uniform" if uniform(S) else ""))
print(f"v4 = v3 + v1 §6 sets <= 60: {dict(c)}; exact fold fails at the chosen k: {bad}")
print("no k in I (set, v3/v1, v5/v4, uniform?):", rest[:15])
print("of these, closed by s6_meeting_uniform:", sum(1 for r in rest if r[3]), "of", len(rest))
