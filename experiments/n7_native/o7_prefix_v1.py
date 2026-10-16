#!/usr/bin/env python3
"""Order seven: the 4-prefix criterion. For a primitive 4-set (v1 < v2 < v3 < v4) let W4 be the longest window on which all
four read in [1/7, 6/7] (one period). If W4 * v4 >= 4/7, then every order-seven set with this prefix (any v5, v6 > v4)
closes with block {1,2,3,4} and the two-runner window on runners 5, 6 (needs 2/(7 v5) + 2/(7 v6) <= 4/(7 v4)).
Lists the 4-prefixes with W4 * v4 < 4/7 (the 'short' prefixes), primitive up to H, with their ratios and W4 * v4, and
checks whether they lie in a bounded ratio region (v4/v1) or form families."""
import math, sys
from itertools import combinations
from collections import Counter
exec(open("o7_map_v1.py").read().split("def classify(")[0])
H = int(sys.argv[1]) if len(sys.argv) > 1 else 60
short = []; tot = 0
for S in combinations(range(1, H + 1), 4):
    if math.gcd(*S) != 1: continue
    tot += 1
    w = max((U - L for L, U in block(S, range(4))), default=0)
    if w * S[3] < 4 / 7 - 1e-12: short.append((round(w * S[3], 4), S))
print(f"primitive 4-prefixes <= {H}: {tot}; short (W4 v4 < 4/7): {len(short)}")
print("  by v4/v1:", sorted(Counter(min(int(S[3] / S[0]), 40) for _, S in short).items()))
print("  by v1:", sorted(Counter(S[0] for _, S in short).items())[:15])
short.sort()
print("  smallest W4 v4:", short[:25])
fam = Counter((S[1] - S[0], S[2] - S[1], S[3] - S[2]) for _, S in short if S[0] == 1)
print("  v1 = 1 short prefixes by gaps (v2-v1, v3-v2, v4-v3):", fam.most_common(15))
