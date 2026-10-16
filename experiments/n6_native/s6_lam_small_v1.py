#!/usr/bin/env python3
"""The c = 1, lam = 1 cases with D = 15..19 (the certificate's root C needs D >= 20). Here v2 = D, v3 = 2D, v1 < 2D/3,
gcd(v1, D) = 1, delta = v1 (v4 = v3 + v1), v5 >= v4 + 1. Conditions are monotone in mu, so it suffices to find a grid
point j/D that works at the largest mu = v4/(3(v4+1)). For each case: the first (kind, m, j) found, or failure."""
from fractions import Fraction as F
import math
def ok(kind, m, p, q4, u, mu):
    if kind == "after":
        return F(1,6) <= p <= F(5,9) and p + F(5,6)*q4 - mu >= m + F(1,6) and p + q4*u/6 + mu <= m + F(5,6)
    if kind == "before":
        return F(4,9) <= p <= F(5,6) and 1 - p + F(5,6)*q4 - mu >= m + F(1,6) and 1 - p + q4*u/6 + mu <= m + F(5,6)
    return F(1,3) + mu/q4 <= p <= F(5,6)*(2 - q4)
res = []; fails = []
for D in range(15, 20):
    for v1 in range(1, D):
        if 3 * v1 >= 2 * D or math.gcd(v1, D) != 1: continue
        v2, v3 = D, 2 * D; v4 = v3 + v1
        if 4 * v2 * v3 <= v4 * (5 * v2 - v3): continue     # uniform: not needed
        q4, u, mu = F(v4, v3), F(2), F(v4, 3 * (v4 + 1))
        hit = next(((k, m, j) for j in range(D) for k in ("after", "before", "sum") for m in range(-2, 3) if ok(k, m, F(j, D), q4, u, mu)), None)
        (res if hit else fails).append(((D, v1), hit))
print(f"c = 1, lam = 1, D = 15..19, not uniform: {len(res) + len(fails)} cases; certified {len(res)}; failing {len(fails)}")
for r in res: print("  ", r)
print("failing:", fails)
