#!/usr/bin/env python3
"""Observation, §5 pair windows: the explicit lap j0 = ceil(v2/(6 v1) - 1/6) (runner 1 enters its first band at the start
of the pair window P_j0) and the uniform condition |P_j0 ∩ runner-1 band| >= 2/(3 v4). By k: share closed by the uniform
pair window at j0; for the rest of the A/B/C sets, the ratio v4/v3 (near-runner?) and whether a 2D phase condition at
some j holds: runner 1 clear across a sub-window and runner 4 clear on a stretch of length v4^-1 * (1/3) * v4/v5 ...
(i.e. class C, the pair-window fold), reported as counts."""
import math, sys, random
from fractions import Fraction as F
from itertools import combinations
from collections import Counter, defaultdict
exec(open("s5_obs_v1.py").read().split("\ndef run(sets")[0])
def uni_j0(S):
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    j0 = max(0, math.ceil(F(v2, 6 * v1) - F(1, 6)))
    if 6 * j0 * D > 4 * v2 - v3: return False
    L, U = F(6 * j0 + 1, 6 * v2), F(6 * j0 + 5, 6 * v3)
    return any(b - a >= F(2, 3 * v4) for a, b in clear_sub(v1, L, U))
def run(sets, label):
    c = defaultdict(Counter); q = defaultdict(list)
    for S in sets:
        v1, v2, v3, v4, v5 = S; D = v3 - v2; k = v1 // D; kb = str(k) if k <= 2 else ">=3"
        if uni_j0(S): c[kb]["uniform at j0"] += 1; continue
        how, j = classify(S)
        c[kb][how] += 1
        if how in ("B", "C"): q[kb].append(float(F(v4, v3)))
    print(f"== {label}")
    for kb in ("1", "2", ">=3"):
        qs = sorted(q[kb]); med = qs[len(qs) // 2] if qs else None
        print(f"   k = {kb}: {dict(sorted(c[kb].items()))}; v4/v3 on B/C: max {max(qs) if qs else None:}, median {med}")
H = int(sys.argv[1]) if len(sys.argv) > 1 else 36
run([S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and s5(S)], f"primitive §5 <= {H}")
random.seed(55); big = []
while len(big) < 2000:
    S = tuple(sorted(random.sample(range(1, 2001), 5)))
    if math.gcd(*S) == 1 and s5(S): big.append(S)
run(big, "random §5 <= 2000")
