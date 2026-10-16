#!/usr/bin/env python3
"""The corner where the large-alpha tree fails: alpha -> 2/5, kappa -> 1/2 (k = 2, v3 -> 3 v1), beta ~ 0.4065, nu ~ 1.1487.
(1) the best loneliness gap  max_t min_i ||v_i t||  for speeds (alpha, 1, 1 + alpha kappa, 1 + beta, (1 + beta) nu) on a fine
grid of (beta, nu) at the corner, to see whether the gap reaches 1/6 only at a point (tight) and where.
(2) integer sets near the corner, (2D, 5D+1, 6D+1, v4, v5): the gap and the exact lonely length."""
import math
from fractions import Fraction as F
def gap(vs, T=12.0, N=400000):
    best = 0; bt = None
    for i in range(1, N):
        t = T * i / N
        g = min(abs(v * t - round(v * t)) for v in vs)
        if g > best: best, bt = g, t
    return best, bt
al, ka = 0.4, 0.5
print("corner speeds / v2:")
for be in (0.40, 0.4033, 0.4065, 0.41, 0.42):
    for nu in (1.14, 1.1487, 1.155):
        vs = [al, 1, 1 + al * ka, 1 + be, (1 + be) * nu]
        g, t = gap([v / al for v in vs], T=6.0, N=300000)
        print(f"  beta {be}, nu {nu}: speeds/v1 {[round(v / al, 4) for v in vs]}, best gap {g:.5f} at t {t:.4f}")
