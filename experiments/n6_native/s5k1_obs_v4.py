#!/usr/bin/env python3
"""§5 k = 1: the sets with no 123-triangle closing window (s5k1_obs_v2 classes F3-only, BOX-only, none), primitive <= H:
relations among v1..v5 -- is v4 = v3 + v1 (v2, v3, v4 an AP of step v1, so x4 = x2 + 2 x1)? v5 = v4 + v1? v5 = 2 v3 + ...?
Also, among all AP sets (v4 = v3 + v1), the share that are exceptions, by a = v2/v1."""
import math, sys
from itertools import combinations
from collections import Counter
from s5k1_obs_v2 import types, k1
H = int(sys.argv[1]) if len(sys.argv) > 1 else 50
rel = Counter(); apstat = Counter(); ex = []
for S in combinations(range(1, H + 1), 5):
    if math.gcd(*S) != 1 or not k1(S): continue
    v1, v2, v3, v4, v5 = S
    ts = types(S)
    tri = any(t.startswith(("W123", "F5", "F4")) for t in ts)
    ap = v4 == v3 + v1
    if ap: apstat[("exception" if not tri else "closed by 123") + (", a<6" if v2 < 6 * v1 else ", a>=6")] += 1
    if not tri:
        rel[("AP v4=v3+v1" if ap else "not AP") + (", v5=v4+v1" if v5 == v4 + v1 else "")] += 1
        if not ap: ex.append(S)
print("exceptions (no 123 window):", dict(rel))
print("non-AP exceptions:", ex[:20])
print("AP sets:", dict(apstat))
