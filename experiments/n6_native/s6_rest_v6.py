#!/usr/bin/env python3
"""Observation. Coprime §6, D < 15, with integrality: v2 = cD, v3 = (c+1)D, delta = v4 - v3 >= 1, Q = 1 + delta/v3,
near-runner Q < 4/(5 - U), v1 = a mod D (unit), lam = delta a^-1 mod D. M = v4/(3 v5) in (0, 1/3] (grid of 240).
List the (D, c, delta, a mod D) cells where the region (after/before windows at meeting times) fails for some M, with the
failing M range, for c <= CMAX; and per c the number of such cells (to see whether they stop)."""
import sys
from fractions import Fraction as F
from collections import Counter
from s6_rest_v4 import closed
CMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 30
cells = []; perc = Counter()
for D in range(2, 15):
    units = [a for a in range(1, D) if __import__("math").gcd(a, D) == 1]
    for c in range(1, CMAX + 1):
        U = F(c + 1, c); v3 = (c + 1) * D; Qmax = 4 / (5 - U)
        d = 1
        while 1 + F(d, v3) < Qmax:
            Q = 1 + F(d, v3)
            for a in units:
                lam = d * pow(a, -1, D) % D
                bad = [F(m, 720) for m in range(1, 241) if not closed(D, lam, U, Q, F(m, 720))]
                if bad:
                    cells.append((D, c, d, a, lam, float(min(bad)), float(max(bad)))); perc[c] += 1
            d += 1
print(f"cells (D, c, delta, a, lam, M_min, M_max) where the region fails for some M, c <= {CMAX}: {len(cells)}")
print("per c:", dict(sorted(perc.items())))
print("per D:", dict(sorted(Counter(x[0] for x in cells).items())))
print("lam values:", dict(Counter((x[4] if x[4] <= x[0] // 2 else x[4] - x[0]) for x in cells)))
for x in cells: print("  ", x[:5], "M in", [round(x[5], 4), round(x[6], 4)])
