#!/usr/bin/env python3
"""Observation: the §5 sets closed by no pair window, fold or cluster box (s5_obs_v1 class F), primitive <= H. For each,
the lap boxes k (runner i in band k_i at a common instant: (6k_i+1) v_j <= (6k_j+5) v_i for all i, j) with k_1 <= 3,
and the smallest such k; then the patterns (v1..v4 fixed, v5 varying) and the v5 range of each pattern."""
import math, sys
from itertools import combinations, product
from collections import defaultdict
exec(open("s5_obs_v1.py").read().split("\ndef run(sets")[0])
def boxes(S, k1max=3):
    v = S; out = []
    for k1 in range(k1max + 1):
        lo = [None] * 5
        # given k1, the instant lies in [(6k1+1)/(6v1), (6k1+5)/(6v1)]; each runner's lap range follows
        L, U = F(6 * k1 + 1, 6 * v[0]), F(6 * k1 + 5, 6 * v[0])
        ranges = [range(k1, k1 + 1)] + [range(int(L * v[i]) - 1, int(U * v[i]) + 1) for i in range(1, 5)]
        for k in product(*ranges):
            if all((6 * k[i] + 1) * v[j] <= (6 * k[j] + 5) * v[i] for i in range(5) for j in range(5)):
                out.append(k)
    return out
H = int(sys.argv[1]) if len(sys.argv) > 1 else 36
pat = defaultdict(list); nobox = []
for S in combinations(range(1, H + 1), 5):
    if math.gcd(*S) != 1 or not s5(S): continue
    if classify(S)[0] != "F": continue
    b = boxes(S)
    pat[S[:4]].append((S[4], b[0] if b else None))
    if not b: nobox.append(S)
for p, l in sorted(pat.items()):
    print(p, "v5 ->", [(x, k) for x, k in l])
print("F sets with no lap box (k1 <= 3):", nobox)
