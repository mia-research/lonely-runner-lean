#!/usr/bin/env python3
"""Exact check (fractions, non-strict bands) of the tight-instant lemmas, r_i = v_i / v1, k = 1 (r3 = 1 + r2):
 TP1 near (1,3,4,5,9): N1 = {14/5 <= r2 <= 17/5, r4 <= 29/5, 43/5 <= r5 <= 47/5}:  r4 <= 5 -> lonely at t = 1/(6 v1);
     r4 >= 5 -> lonely at t = 5/(6 v1).
 TP2 near (1,2,3,4,5): N2 = {2 < r2 <= 11/5, 19/5 <= r4 <= 23/5, r5 <= 29/5}: r5 <= 5 -> t = 1/(6 v1); r5 >= 5 -> t = 5/(6 v1).
Checks every integer k = 1 set (v1 <= 60, ordered) in N1 or N2: the named instant is lonely (all readings in
[1/6, 5/6] mod 1, endpoints included)."""
import math
from fractions import Fraction as F
def ok(S, t):
    return all(F(1, 6) <= (v * t) % 1 <= F(5, 6) for v in S)
c1 = c2 = bad = 0
for v1 in range(1, 61):
    for v2 in range(2 * v1 + 1, int(3.4 * v1) + 2):
        v3 = v1 + v2
        for v4 in range(v3 + 1, int(5.8 * v1) + 2):
            for v5 in range(v4 + 1, int(9.4 * v1) + 2):
                S = (v1, v2, v3, v4, v5); r = [F(v, v1) for v in S]
                if F(14, 5) <= r[1] <= F(17, 5) and r[3] <= F(29, 5) and F(43, 5) <= r[4] <= F(47, 5):
                    c1 += 1
                    t = F(1, 6 * v1) if r[3] <= 5 else F(5, 6 * v1)
                    if not ok(S, t): bad += 1; print("TP1 fails", S)
                if r[1] <= F(11, 5) and F(19, 5) <= r[3] <= F(23, 5) and r[4] <= F(29, 5):
                    c2 += 1
                    t = F(1, 6 * v1) if r[4] <= 5 else F(5, 6 * v1)
                    if not ok(S, t): bad += 1; print("TP2 fails", S)
print(f"N1 sets {c1}, N2 sets {c2}, failures {bad}")
