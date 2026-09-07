"""
Is "no tight instance contains a multiple of n" a general fact, or an n=8 accident?

Tight instance at n: T = n-1 distinct positive integers, gcd 1, M(T) = 1/n exactly.
Enumerated exhaustively at n = 3,4,5,6,7 (cheap) and cross-checked at n = 8.
Exact rational arithmetic; tightness decided by exact interval coverage.

Note the ONE-WAY direction that is trivial and must not be mistaken for the claim:
if n divides no element of T then t = 1/n gives ||v t|| >= 1/n, so M(T) >= 1/n.
The claim under test is the CONVERSE-flavoured one -- that M(T) = 1/n FORCES
n to divide nothing -- and that is not trivial.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import sys

def covered(T, n):
    """True iff the closed bad sets cover [0,1], i.e. M(T) <= 1/n, i.e. (with LRC) = 1/n."""
    iv=[]
    for v in T:
        w=F(1,n*v)
        for k in range(0,v+1):
            lo,hi=F(k,v)-w,F(k,v)+w
            if hi<=0 or lo>=1: continue
            iv.append((max(lo,F(0)),min(hi,F(1))))
    iv.sort(); cur=F(0)
    for lo,hi in iv:
        if lo>cur: return False
        if hi>cur: cur=hi
    return cur>=1

def maximal_levels(n):
    qs=list(range(2,n))
    return [q for q in qs if not any(q2%q==0 and q2!=q for q2 in qs)]

def run(n, V):
    lv=maximal_levels(n)
    tight=[]; withmult=[]
    for T in combinations(range(1,V+1), n-1):
        if lv and not all(any(v%q==0 for v in T) for q in lv): continue
        g=0
        for v in T: g=gcd(g,v)
        if g!=1: continue
        if covered(T,n):
            tight.append(T)
            if any(v%n==0 for v in T): withmult.append(T)
    print(f"n={n}, speeds<={V}: {len(tight)} tight instances; "
          f"{len(withmult)} of them contain a multiple of {n}")
    for T in tight[:12]:
        print(f"    {T}{'   <-- CONTAINS MULTIPLE OF n' if any(v%n==0 for v in T) else ''}")
    if len(tight)>12: print(f"    ... ({len(tight)-12} more)")
    return tight, withmult

if __name__=="__main__":
    tot=0
    for n,V in ((3,30),(4,30),(5,30),(6,28),(7,26),(8,22)):
        t,w=run(n,V); tot+=len(w); print()
    print(f"TOTAL tight instances found containing a multiple of n: {tot}")
