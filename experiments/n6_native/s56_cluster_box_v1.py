#!/usr/bin/env python3
"""Check of a parametric lap box for the run family (1, 3k+2, 3k+3, 3k+4, 3k+5): laps (0, m, m, m, m), m = ceil(k/2).
Box conditions (6 k_i + 1) v_j <= (6 k_j + 5) v_i reduce to: v5 <= 6m + 5 (runner 1 against the fastest),
(6m+1) <= 5 v2, and v5/v2 <= (6m+5)/(6m+1) (the cluster's spread). Exact check for k = 2..2000, and the general
cluster region it implies (one slow runner, four runners within ratio (6m+5)/(6m+1) of each other in [ (6m+1)/5, 6m+5 ])."""
from fractions import Fraction as F
def box(S, k): return all((6 * k[i] + 1) * S[j] <= (6 * k[j] + 5) * S[i] for i in range(5) for j in range(5))
ok = 0; bad = []
for kk in range(2, 2001):
    S = (1, 3 * kk + 2, 3 * kk + 3, 3 * kk + 4, 3 * kk + 5); m = -(-kk // 2)
    if box(S, (0, m, m, m, m)): ok += 1
    else: bad.append(kk)
print(f"run family k = 2..2000: box (0,m,m,m,m), m = ceil(k/2), holds in {ok}; fails at {bad[:10]}")
print("k = 1, (1,5,6,7,8): box (0,2,2,3,3) holds:", box((1, 5, 6, 7, 8), (0, 2, 2, 3, 3)))
