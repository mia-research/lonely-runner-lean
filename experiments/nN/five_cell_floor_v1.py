"""Longest lonely cell at 1/8 of a five-disparity set, times its maximum: the exhaustive floor.

fast_pair_v1 reports "minimum 1/4, at the progressions (1..5)k" from 20,000 RANDOM 5-sets of [1,40]
(a 3% sample of C(40,5)).  This pass is exhaustive over the primitive 5-subsets of [1,B], exact in
fractions.  Integer speeds have period 1; a cell is a maximal closed interval of [0,1] on which every
d has circDist(d t) >= 1/8 (inclusive: a point exactly at 1/8 is clear), including degenerate cells.
Independent check of the minimiser on a 2,000,000-point grid is at the end.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce
import sys, time

def cells(S, n=8):
    r = F(1, n); bad = []
    for d in S:
        for j in range(d + 1):
            bad.append((F(j, d) - r / d, F(j, d) + r / d))   # open blocked intervals
    bad.sort(); out = []; cur = F(0)
    for a, b in bad:
        if a > cur: out.append((cur, a))
        elif a == cur and a > 0 and (not out or out[-1][1] != cur): out.append((cur, cur))
        cur = max(cur, b)
        if cur >= 1: break
    return [(a, b) for a, b in out if 0 < a and b < 1]

def longest(S): return max((b - a for a, b in cells(S)), default=F(0))

B = int(sys.argv[1]) if len(sys.argv) > 1 else 30
t0 = time.time()
for S in [(1, 2, 3, 4, 5), (2, 4, 6, 8, 10)]:
    print(f"progression {S}: longest*max = {longest(S) * max(S)}")
res = sorted((longest(S) * max(S), S) for S in combinations(range(1, B + 1), 5) if reduce(gcd, S) == 1)
print(f"primitive 5-subsets of [1,{B}]: {len(res)}")
print(f"count with longest*max < 1/4: {sum(1 for v, _ in res if v < F(1, 4))}")
for v, S in res[:12]:
    print(f"  {S}: longest*max = {v} = {float(v):.5f}")
S = res[0][1]; N = 2_000_000
cd = lambda x: min(x % 1, 1 - x % 1)
ok = [i / N for i in range(1, N) if all(cd(d * i / N) >= 1 / 8 - 1e-12 for d in S)]
runs = []; s = p = ok[0]
for t in ok[1:]:
    if t - p > 1.5 / N: runs.append(p - s); s = t
    p = t
runs.append(p - s)
print(f"grid check {S}: longest ~ {max(runs):.6f}, times max = {max(runs) * max(S):.5f}")
print(f"({time.time() - t0:.0f}s)")
