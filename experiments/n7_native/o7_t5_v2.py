#!/usr/bin/env python3
"""Phase 2: exact kappa = v5 W5 for the 5-prefixes below 5/28 (o7_t5_v1_60.out), the exact window of the triple
(3, 4, 5) at 1/7 (the 5/28 level: any prefix containing c (3,4,5) with v5 = 5c has kappa <= 5 W(3,4,5)), and the
count of 5-prefixes <= 60 at kappa < 5/28 and = 5/28 (floats, EPS 1e-9)."""
import math, re
from fractions import Fraction as Fr
def bf(v): return [(Fr(7 * m + 1, 7 * v), Fr(7 * m + 6, 7 * v)) for m in range(v)]
def W(P):
    cur = bf(P[0])
    for v in P[1:]:
        B = bf(v); i = j = 0; out = []
        while i < len(cur) and j < len(B):
            lo, hi = max(cur[i][0], B[j][0]), min(cur[i][1], B[j][1])
            if hi > lo: out.append((lo, hi))
            if cur[i][1] < B[j][1]: i += 1
            else: j += 1
        cur = out
    return max((h - l for l, h in cur), default=Fr(0))
print("W(3,4,5) =", W((3, 4, 5)), " 5 W(3,4,5) =", 5 * W((3, 4, 5)))
low = re.findall(r"\(([0-9.]+), \(([0-9, ]+)\)\)", open("o7_t5_v1_60.out").read().split("40 smallest kappa:")[1].split("\n")[0])
for k, P in low:
    P = tuple(map(int, P.split(",")))
    kap = P[4] * W(P)
    if kap < Fr(5, 28): print(f"   {P}: kappa = {kap}, rho = 2/(7 kappa) = {Fr(2, 7) / kap}")
