#!/usr/bin/env python3
"""§5 k = 1 exceptions (no 123-triangle window), primitive <= H, split into the AP family (v4 = v3 + v1) and the rest;
for each: the available types, the earliest F3 window (laps of runners 1, 2, 4, 5 and x1 at its start) and the earliest
BOX window (laps); for the rest, also v2/v1 and (v4 - v3, v5 - v3)/v1."""
import math, sys
from itertools import combinations
from collections import Counter
from s5k1_obs_v2 import types, k1, block
H = int(sys.argv[1]) if len(sys.argv) > 1 else 50
fam = {"AP": [], "other": []}
for S in combinations(range(1, H + 1), 5):
    if math.gcd(*S) != 1 or not k1(S): continue
    ts = types(S)
    if any(t.startswith(("W123", "F5", "F4")) for t in ts): continue
    v1, v2, v3, v4, v5 = S
    T = 3 / v1
    f3 = [(round(L * v1, 3), ms) for L, U, ms in block([v1, v2, v4, v5], T) if v3 * (U - L) >= 1 / 3 - 1e-12][:1]
    bx = [(round(L * v1, 3), ms) for L, U, ms in block(list(S), 6 / v1)][:1]
    fam["AP" if v4 == v3 + v1 else "other"].append((S, sorted(ts), f3, bx))
for k, l in fam.items():
    print(f"== {k}: {len(l)}")
    print("   types:", Counter(tuple(x[1]) for x in l).most_common(5))
    print("   F3 laps (runners 1,2,4,5):", Counter(tuple(x[2][0][1]) for x in l if x[2]).most_common(6))
    print("   BOX laps:", Counter(tuple(x[3][0][1]) for x in l if x[3]).most_common(6))
    for x in l[:8]: print("    ", x[0], "a=%.2f" % (x[0][1] / x[0][0]), "(v4-v3, v5-v3)/v1 = (%.2f, %.2f)" % ((x[0][3] - x[0][2]) / x[0][0], (x[0][4] - x[0][2]) / x[0][0]), x[1], x[2], x[3])
