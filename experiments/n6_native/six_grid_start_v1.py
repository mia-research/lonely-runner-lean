#!/usr/bin/env python3
"""Step 1: the grid start. D = c(1,2,3,4,5) is lonely (threshold 1/6) in [0, 2/c) exactly at c t in {1/6, 5/6, 7/6, 11/6}.
Prediction: at c t = 1/6 (+ lap) runner 1 enters and runner 5 leaves its band, so the point opens into an interval
iff d5 < 5 d1; at c t = 5/6 (+ lap) roles swap, opens iff d5 > 5 d1. Runners 2-4 are strictly inside their bands.
Test: random small rational perturbations of all five speeds; for each grid point, find whether the perturbed
lonely set has an interval near it (exact interval intersection in a small neighbourhood), compare with the rule.
Also checks the exact grid lonely set is these four points."""
import random
from fractions import Fraction as F
sixth = F(1, 6)
def lonely_intervals(V, lo, hi):
    ivs = [(lo, hi)]
    for v in V:
        new = []
        for a, b in ivs:
            k = max(int(a * v - sixth) - 1, 0)
            while True:
                l, r = (k + sixth) / v, (k + 5 * sixth) / v
                if l > b: break
                L, R = max(a, l), min(b, r)
                if L <= R: new.append((L, R))
                k += 1
        ivs = new
    return ivs
rng = random.Random(7)
c = 12
grid = [F(c * k) for k in range(1, 6)]
pts = lonely_intervals(grid, F(0), F(2, c) - F(1, 10**6))
print("grid lonely set in [0, 2/c):", [(str(a), str(b)) for a, b in pts])
trials = mism = 0; opened_count = {}
for _ in range(4000):
    eps = [F(rng.randint(-1000, 1000), 10**6) for _ in range(5)]
    V = [g + e for g, e in zip(grid, eps)]
    if len(set(V)) < 5 or V[4] == 5 * V[0]: continue
    trials += 1
    opened = []
    for u, rule in ((F(1, 6), V[4] < 5 * V[0]), (F(5, 6), V[4] > 5 * V[0]), (F(7, 6), V[4] < 5 * V[0]), (F(11, 6), V[4] > 5 * V[0])):
        t0 = u / c; d = F(1, 400 * c)
        has = any(b > a for a, b in lonely_intervals(V, t0 - d, t0 + d))
        opened.append(has)
        mism += has != rule
    opened_count[tuple(opened)] = opened_count.get(tuple(opened), 0) + 1
print(f"perturbations: {trials}; mismatches with the rule (4 points each): {mism}")
print("which grid points opened (1/6, 5/6, 7/6, 11/6):", opened_count)
