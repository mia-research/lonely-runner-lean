"""Coverage by openings counted from the TOP: j = e - r, small r.

The one instance that worked (the ratio condition) is j = e-1, i.e. r = 1.  The earlier
coverage sweep counted k from 0 and found the requirement unbounded -- but that is the wrong
end.  At j = e-r we have a = 5(e-r)+1 = 5e-(5r-1), so d*a = -d(5r-1) mod 5e, and the band is
    e <= d(5r-1) mod 5e <= 4e,
which for the first wrap reads  e/(5r-1) <= d <= 4e/(5r-1).
So r indexes a family of bands marching down from [e/4, e].  How far does small r get?
"""
import math
from itertools import combinations

def works_at(c, e, j, n=5):
    M = n*e
    return all(e <= (d*(n*j+1)) % M <= (n-1)*e for d in c)

def min_r(c, n=5):
    """smallest r >= 1 with opening j = e-r settling the set; None if none."""
    e = c[-1]
    for r in range(1, e+1):
        if works_at(c, e, e-r, n): return r
    return None

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

for hi in (40, 60):
    tot = 0
    from collections import Counter
    dist = Counter(); none = 0; worst = 0; wset = None
    for c in combinations(range(1,hi+1), 4):
        if not prim(c): continue
        tot += 1
        r = min_r(c)
        if r is None: none += 1
        else:
            dist[r] += 1
            if r > worst: worst, wset = r, c
    print(f"n=5, exhaustive primitive 4-subsets of [1,{hi}]: {tot} sets")
    cum = 0
    for R in (1,2,3,4,5,6,8,10,15,20,30,50):
        cum = sum(v for k,v in dist.items() if k <= R)
        print(f"   settled by some j = e-r with r <= {R:<3}: {cum:>8}  ({100*cum/tot:6.2f}%)")
    print(f"   never settled from the top: {none}")
    print(f"   worst r needed: {worst} at {wset}")
    print()
