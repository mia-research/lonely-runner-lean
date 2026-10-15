#!/usr/bin/env python3
"""E54: the three-way closure of G4/G7, checked on every exceptional §7 set to 120. Case (i) v5 <= 5 v1: lonely at
1/(6 v1). Case (ii) v4 <= 5 v1, 7 v4 <= 5 v5, v5 <= 11 v1: lonely at max(1/(6 v1), 7/(6 v5)). Case (iii) otherwise: the
named window W (W4 or W7) meets window_two's thresholds: 1/(3v4) + 1/(3v5) <= W and (m + 1/3)/v5 <= W for every
integer m with 3 m v4 < v4 + v5. Reports each case's count and any failure."""
from fractions import Fraction as F
from collections import Counter
def frac(z): return z - (z.numerator // z.denominator)
def lonely(S, t): return all(F(1, 6) <= frac(d * t) <= F(5, 6) for d in S)
c = Counter(); bad = []
for line in open("s7_exceptional_v2_120.out"):
    if not line.startswith("EXC"): continue
    v1, v2, v3, v4, v5, nn, rel = map(int, line.split()[1:8]); S = (v1, v2, v3, v4, v5)
    g = "G4" if nn == 4 else "G7"
    if v5 <= 5 * v1:
        ok = lonely(S, F(1, 6 * v1)); c[(g, "(i)", ok)] += 1
    elif v4 <= 5 * v1 and 7 * v4 <= 5 * v5 and v5 <= 11 * v1:
        ok = lonely(S, max(F(1, 6 * v1), F(7, 6 * v5))); c[(g, "(ii)", ok)] += 1
    else:
        W = F(1, 3 * v3) + F(1, 12 * v1) if g == "G4" else F(11, 42 * v3) + min(F(17, 42 * v3), F(5, 42 * v1))
        ok = F(1, 3 * v4) + F(1, 3 * v5) <= W and all((m + F(1, 3)) / v5 <= W for m in range(1, v5) if 3 * m * v4 < v4 + v5)
        c[(g, "(iii)", ok)] += 1
    if not ok: bad.append(S)
for k, v in sorted(c.items()): print(v, k)
print("failures:", bad[:10], len(bad))
