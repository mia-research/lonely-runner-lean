r"""
ok_finite_red_v2 -- min |G| over Case 2, as speeds are forced large.  Interval arithmetic:
G(E) = intersection over e of { t in [0,1) : ||e t|| >= 1/8 }, each a union of e closed arcs
[ (8j+1)/(8e), (8j+7)/(8e) ].  Intersecting incrementally keeps the interval count <= sum e.
Exact Fractions throughout.  |G| > 0 is precisely the witness condition (boundary included).

u is scale-invariant, so size matters only against gcd(E) = 1.  If min |G| grows with the
speed floor B, Case 2 reduces to a finite check and the architecture is:
    (a) max(E) >= B  ==>  |G| bounded below;   (b) finite check under B.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd
import random, sys

def arcs(e):
    return [(F(8*j+1,8*e), F(8*j+7,8*e)) for j in range(e)]

def inter(A,B):
    out=[]; i=j=0
    while i<len(A) and j<len(B):
        lo=max(A[i][0],B[j][0]); hi=min(A[i][1],B[j][1])
        if lo<hi: out.append((lo,hi))
        if A[i][1]<B[j][1]: i+=1
        else: j+=1
    return out

def G_measure(E):
    cur=arcs(E[0])
    for e in E[1:]:
        cur=inter(cur,arcs(e))
        if not cur: return F(0)
    return sum((b-a for a,b in cur), F(0))

random.seed(5)
print(f"{'floor B':>8} {'#tuples':>9} {'min |G|':>16} {'~':>11}  argmin")
for B,TOP,NS in [(1,26,None),(2,30,None),(6,34,6000),(12,44,6000),(25,60,5000),(50,90,4000)]:
    cand=[]
    if NS is None:
        cand=[E for E in combinations(range(B,TOP+1),7)
              if reduce(gcd,E)==1 and any(e%8==0 for e in E)]
    else:
        seen=set()
        tries=0
        while len(cand)<NS and tries<NS*60:
            tries+=1
            E=tuple(sorted(random.sample(range(B,TOP+1),7)))
            if E in seen: continue
            seen.add(E)
            if reduce(gcd,E)==1 and any(e%8==0 for e in E): cand.append(E)
    best=None
    for E in cand:
        g=G_measure(list(E))
        if best is None or g<best[0]: best=(g,E)
    g,E=best
    print(f"{B:>8} {len(cand):>9} {str(g):>16} {float(g):11.8f}  {E}")
print("\n|G| = 0 anywhere would refute LRC(8); the minimum is the sharp constant to prove.")
