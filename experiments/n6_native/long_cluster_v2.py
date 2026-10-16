#!/usr/bin/env python3
"""Observation only. The longest cascades have the cluster ending exactly at a multiple of n (relative to the slow runner):
(1,17..21) at n=7 ends at 21 = 3*7; (1,10..14) at 14; (1,9..12) at n=6 ends at 12; (1,23,25,48) at n=5 has 25. Family
(1, nj-k+1, ..., nj) with k = n-2 (a consecutive run ending on a multiple of n): moves and landing as j grows; control: the
same run shifted by one (ending at nj+1) and by -1 (ending at nj-1)."""
import math
from fractions import Fraction as F
exec(open("long_cluster_v1.py").read().split("for k, step")[0])
for n in (5, 6, 7):
    k = n - 2
    for shift, lab in ((0, "ends on nj"), (-1, "ends on nj-1"), (1, "ends on nj+1")):
        out = []
        for j in range(1, 41):
            top = n * j + shift; S = tuple([1] + list(range(top - k + 1, top + 1)))
            if S[1] <= 1 or math.gcd(*S) != 1: continue
            mv, R, one = walk(S, n); out.append((j, mv, R))
        print(f"n={n} run of {k} {lab}: moves for j=1..40:", [m for _, m, _ in out], "max", max(m for _, m, _ in out))
