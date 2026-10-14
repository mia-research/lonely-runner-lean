"""The rational witness a/q is native (exhibit an instant; no cap, no move count, no uniformity).
Its only parameter is the denominator q.  How does the required q behave with the order?

The band [1/n, 1-1/n] WIDENS with n -- each blocker excludes 2/n -- while the number of blockers
grows as n-2.  Which wins is a fact, not an argument, so measure it.
"""
from fractions import Fraction as F
from itertools import combinations
import math, collections
def min_q(ds, n, Q=120):
    for q in range(2, Q+1):
        for a in range(1, q):
            if math.gcd(a,q) != 1: continue
            if all(F(1,n) <= min(F((d*a)%q,q), 1-F((d*a)%q,q)) for d in ds): return q
    return None
for n, HI in ((5,26),(6,20),(7,15),(8,13)):
    k = n-1; dist = collections.Counter(); worst = 0; arg = None; tot = 0; fail = 0
    for c in combinations(range(1,HI+1), k):
        g=c[0]
        for x in c[1:]: g=math.gcd(g,x)
        if g!=1: continue
        tot+=1
        q = min_q(c, n)
        if q is None: fail+=1; continue
        dist[q]+=1
        if q > worst: worst, arg = q, c
    print(f"n={n}  ({k} disparities)  primitive {k}-sets in [1,{HI}]: {tot}")
    print(f"   max smallest-working denominator q : {worst}   at {arg}"
          f"{'   (none found for ' + str(fail) + ')' if fail else ''}")
    print(f"   distribution: {dict(sorted(dist.items())[:12])}{' ...' if len(dist)>12 else ''}")
    print()
