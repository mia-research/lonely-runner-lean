#!/usr/bin/env python3
"""§8 exceptions ([1,60]): explain each exactly.
Path A: (1,0) -> (5,1) -> (4,1), runner j in {2,3} blocks at (4,1). Conditions, each exact from the
step rules: v5 in (5 v1, 7 v1) [first move], 7 v4 > 5 v5 [step on, s8_v4_steps_on], 5 v4 < 7 v_j
[s8_slow_blocks_at_v4]. Chained: v_j > (25/49) v5 > (125/49) v1.
Checks every exception on path A satisfies all three and v_j > 125 v1/49; lists the others in full,
with the blockers at each state and the reading of each element."""
import sys, math, importlib.util
from fractions import Fraction as F
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
nA = okA = 0; others = []; minratio = None
for v1 in range(1, HI):
    for v2 in range(v1 + 1, min(3 * v1, HI) + 1):
        for v3 in range(v2 + 1, min(3 * v1, HI) + 1):
            for v4 in range(v3 + 1, HI + 1):
                for v5 in range(v4 + 1, HI + 1):
                    S = (v1, v2, v3, v4, v5)
                    if math.gcd(*S) != 1 or not r.six_residual(S): continue
                    W = walk(S)
                    slow = next((k for k, (st, b, t) in enumerate(W) if any(x <= 3 for x in b)), None)
                    if slow is None: continue
                    path = [st for st, _, _ in W[:slow + 1]]
                    if path == [(1, 0), (5, 1), (4, 1)]:
                        nA += 1
                        js = [x for x in W[slow][1] if x <= 3]
                        conds = (5 * v1 < v5 < 7 * v1) and 7 * v4 > 5 * v5 and all(5 * v4 < 7 * S[j - 1] for j in js) \
                                and all(F(S[j - 1], v1) > F(125, 49) for j in js)
                        okA += conds
                        for j in js:
                            q = F(S[j - 1], v1)
                            if minratio is None or q < minratio[0]: minratio = (q, S)
                    else:
                        others.append((S, [(st, b, str(t), [str(d * t) for d in S]) for st, b, t in W[:slow + 1]]))
print(f"HI={HI}: §8 exceptions on path (1,0)->(5,1)->(4,1): {nA}; all three step conditions and v_j > 125 v1/49 hold: {okA}")
print(f"  smallest blocking v_j/v1 observed: {minratio[0]} = {float(minratio[0]):.3f} at {minratio[1]} (bound 125/49 = {125/49:.3f})")
print(f"  exceptions on other paths: {len(others)}")
for S, info in others:
    print("   ", S)
    for st, b, t, reads in info: print("       state", st, "blockers", b, "t =", t, "readings", reads)
