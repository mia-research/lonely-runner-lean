#!/usr/bin/env python3
"""Observation: §5 sets not closed by the uniform pair window (s5_coverage_v1). Test the pair-window four-block fold:
runners 2, 3 on one lap j clear on [(j+1/6)/v2, (j+5/6)/v3]; runners 1 and 4 clear on a common sub-window W (any laps);
runner 5 folded (v5 |W| >= 1/3). Also the same with runners 4 and 5 swapped (5 in the block, 4 folded)."""
import math, sys
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("s5_coverage_v1.py").read().split("\ndef run(sets, label):")[0])
def clear_sub(v, L, U):
    out = []
    for m in range(int(L * v) - 1, int(U * v) + 2):
        a = max(L, F(6 * m + 1, 6 * v)); b = min(U, F(6 * m + 5, 6 * v))
        if a <= b: out.append((a, b))
    return out
def pair_fold(S):
    v1, v2, v3, v4, v5 = S
    for j in range(0, 4 * v2 // v1 + 2):
        L, U = F(6 * j + 1, 6 * v2), F(6 * j + 5, 6 * v3)
        if L > U: continue
        for a1, b1 in clear_sub(v1, L, U):
            for x, y, fv in ((v4, v5, v5), (v5, v4, v4)):
                for a, b in clear_sub(x, a1, b1):
                    if fv * (b - a) >= F(1, 3): return True
    return False
H = int(sys.argv[1]) if len(sys.argv) > 1 else 30
sets = [S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and s5(S) and not uni(S, range(0, 4 * S[1] // S[0] + 2))]
c = Counter(); miss = []
for S in sets:
    if pair_fold(S): c["pair-window fold"] += 1
    else: c["not"] += 1; miss.append(S)
print(f"§5 <= {H} not closed by the uniform pair window: {len(sets)}: {dict(c)}; not closed {miss[:15]}")
