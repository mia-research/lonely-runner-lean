"""The wrong tool.  Every criterion so far searched FLANK openings (j+1/n)/e -- instants tied to
a disparity.  But a lonely instant need not be tied to anything: t = a/q is lonely exactly when
(d*a mod q)/q lies in [1/n, 1-1/n] for every d.  q = 2 asks that every disparity be odd, q = 3
that none be divisible by 3, q = n that none be divisible by n (which is P1').

Question that decides whether this is a proof route: is the required denominator BOUNDED?
"""
from fractions import Fraction as F
from itertools import combinations
import math, collections
n = 5
def lonely_at(ds, a, q):
    for d in ds:
        r = (d * a) % q
        if not (F(1,n) <= min(F(r,q), 1 - F(r,q))): return False
    return True
def min_q(ds, Q):
    for q in range(2, Q+1):
        for a in range(1, q):
            if math.gcd(a,q) != 1: continue
            if lonely_at(ds, a, q): return q
    return None
for HI in (20, 30, 40, 50):
    dist = collections.Counter(); tot = 0; worst = 0; arg = None; fail = []
    for c in combinations(range(1, HI+1), 4):
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        tot += 1
        q = min_q(c, 60)
        if q is None: fail.append(c); continue
        dist[q] += 1
        if q > worst: worst, arg = q, c
    print(f"[1,{HI:>2}]  {tot:>7} primitive 4-sets")
    print(f"        smallest working denominator q: max = {worst}  at {arg}")
    print(f"        distribution: {dict(sorted(dist.items()))}")
    print(f"        no q <= 60 works: {len(fail)}   {fail[:4]}")
    print()
