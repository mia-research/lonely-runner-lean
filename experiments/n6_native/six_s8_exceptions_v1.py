#!/usr/bin/env python3
"""§8 exceptions (walk(S) != walk({v1,v4,v5})), [1, HI]. For each: the first state of the full walk at which
one of v1, v2, v3 is in the way, the slow rank(s) blocked, and the path so far. Tests the rule: at state
(4, 1) (opening 1 of v4) runner 3 is in the way iff 5 v4 < 7 v3, and runner 2 iff 5 v4 < 7 v2; and checks
over ALL §8 sets whose walk visits (4, 1) that the rule predicts exactly when runner 2 or 3 blocks there."""
import sys, math, importlib.util
from fractions import Fraction as F
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1])
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def walk(S):
    t = F(1, 6 * S[0]); state = (1, 0); out = []
    while True:
        blk = [S.index(d) + 1 for d in S if cd(d * t) < F(1, 6)]
        out.append((state, tuple(blk), t))
        if not blk: return out
        best = None
        for i in blk:
            d = S[i - 1]; N = round(d * t); o = F(6 * N + 1, 6 * d)
            if best is None or o > best[0]: best = (o, i, N)
        t = best[0]; state = (best[1], best[2])
first_slow = Counter(); paths = Counter(); exc = 0; visits = rule_bad = 0
for v1 in range(1, HI):
    for v2 in range(v1 + 1, min(3 * v1, HI) + 1):
        for v3 in range(v2 + 1, min(3 * v1, HI) + 1):
            for v4 in range(v3 + 1, HI + 1):
                for v5 in range(v4 + 1, HI + 1):
                    S = (v1, v2, v3, v4, v5)
                    if math.gcd(*S) != 1 or not r.six_residual(S): continue
                    W = walk(S)
                    for state, blk, t in W:
                        if state == (4, 1):
                            visits += 1
                            pred = tuple(x for x in (2, 3) if 5 * v4 < 7 * S[x - 1])
                            got = tuple(x for x in blk if x in (2, 3))
                            rule_bad += pred != got
                    slow = next(((state, tuple(b for b in blk if b <= 3)) for state, blk, t in W if any(b <= 3 for b in blk)), None)
                    if slow:
                        exc += 1; first_slow[slow] += 1
                        paths[tuple(s for s, _, _ in W[:[s for s, _, _ in W].index(slow[0]) + 1])] += 1
print(f"HI={HI}: §8 sets where a slow runner is ever in the way: {exc}")
print("  first such (state, slow ranks in the way):", first_slow.most_common(8))
print("  path up to that state:", paths.most_common(5))
print(f"  states (4,1) visited over all §8 sets: {visits}; mismatches of 'runner j blocks iff 5 v4 < 7 v_j' (j = 2, 3): {rule_bad}")
