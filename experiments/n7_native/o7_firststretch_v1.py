#!/usr/bin/env python3
"""First-stretch property, EXACT, parallel: every primitive six-set v1 < ... < v6 <= H has a lonely instant at 1/7 in
the first band stretch of the slowest runner, t in [1/(7 v1), 6/(7 v1)].  Also records the largest 'first lonely
position' theta* = v1 * (first lonely instant >= 1/(7 v1)) in units of runner 1's lap."""
import math, sys
from fractions import Fraction as Fr
from itertools import combinations
from multiprocessing import Pool
from o7_exact import lcm, inter
def first_theta(S):
    M = lcm(S); N = 7 * M; cur = None
    for v in S:
        q = M // v; B = [((7 * m + 1) * q, (7 * m + 6) * q) for m in range(v)]
        cur = B if cur is None else inter(cur, B, strict=False)
    lo = Fr(N, 7 * S[0])
    for L, U in cur:
        if U >= lo: return max(Fr(L), lo) * S[0] / N     # theta in runner-1 laps
    return None
def work(args):
    v1, H = args; bad = []; worst = (Fr(0), None); n = 0
    for rest in combinations(range(v1 + 1, H + 1), 5):
        S = (v1,) + rest
        if math.gcd(*S) != 1: continue
        n += 1; th = first_theta(S)
        if th is None or th > Fr(6, 7): bad.append(S)
        elif th > worst[0]: worst = (th, S)
    return n, bad, worst
if __name__ == "__main__":
    H = int(sys.argv[1])
    with Pool(10) as pool: res = pool.map(work, [(v1, H) for v1 in range(1, H - 4)], chunksize=1)
    n = sum(r[0] for r in res); bad = [s for r in res for s in r[1]]; worst = max((r[2] for r in res if r[2][1]), key=lambda z: z[0])
    print(f"primitive six-sets <= {H}: {n}; not lonely in the first stretch of v1: {len(bad)} {bad[:10]}")
    print(f"   latest first-lonely position theta* (runner-1 laps): {worst[0]} = {float(worst[0]):.4f} at {worst[1]}")
