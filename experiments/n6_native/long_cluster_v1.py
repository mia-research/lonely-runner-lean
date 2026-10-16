#!/usr/bin/env python3
"""Observation only. The longest cascades (long_cascades_v1) pair one slow runner with a cluster of near-equal fast
speeds that take the knot in turn, each one lap higher. Test: families (1, w, w+1, ..., w+k-1) at order n = k+2 (all
runners used), moves and landing as w grows; and the same with the cluster spread doubled (step 2)."""
import math
from fractions import Fraction as F
def walk(S, n):
    rho = [F(d, S[0]) for d in S]; R = F(1); mv = 0; one = 0
    while True:
        Z = [(y, j) for y in range(len(S)) for j in [round(R * rho[y] / n)] if j >= 1 and n * j - 1 < R * rho[y] < n * j + 1]
        if not Z: return mv, R, one
        one += len(Z) == 1
        R = max(F(n * j + 1) / rho[y] for y, j in Z); mv += 1
for k, step in ((3, 1), (4, 1), (5, 1), (4, 2), (5, 2)):
    n = k + 2; out = []
    for w in list(range(2, 60)) + [80, 100, 150, 200, 300, 500, 1000]:
        S = tuple([1] + [w + step * i for i in range(k)])
        if math.gcd(*S) != 1: continue
        mv, R, one = walk(S, n); out.append((w, mv))
    best = max(out, key=lambda z: z[1])
    print(f"n={n}, cluster of {k} with step {step}: max moves {best[1]} at w={best[0]}; moves by w (w: moves):",
          ", ".join(f"{w}:{m}" for w, m in out if m >= best[1] - 3 or w in (100, 200, 500, 1000)))
