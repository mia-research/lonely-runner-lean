#!/usr/bin/env python3
"""WHERE the isolation points are, not how big they are.

Once a runner is off the grid, its witnesses are no longer at t = a/8. Track, for every
runner, the LOCATION of its isolation set in ORIGINAL time units, and how far that is from
the nearest grid time a/8.  (Period is q in original units, so grid times are a/8 for odd a
up to 8q.)
"""
from fractions import Fraction as F
from functools import reduce
from math import gcd, lcm

def bsm_good(S):
    iv=[]
    for s in S:
        for k in range(0,s+1):
            lo,hi=max(F(8*k-1,8*s),F(0)),min(F(8*k+1,8*s),F(1))
            if lo<hi: iv.append((lo,hi))
    iv.sort(); m=[]
    for lo,hi in iv:
        if m and lo<m[-1][1]: m[-1][1]=max(m[-1][1],hi)
        else: m.append([lo,hi])
    g=[]; cur=F(0)
    for lo,hi in m:
        if cur<=lo: g.append((cur,lo))
        cur=max(cur,hi)
    if cur<=1: g.append((cur,F(1)))
    return [(a,b) for a,b in g if a<=b and not(a==b==0) and not(a==b==1)]
def clear(V):
    q=reduce(lcm,[x.denominator for x in V]); E=[int(x*q) for x in V]
    g=reduce(gcd,E); return [e//g for e in E], q//g
def drift(G,q):
    """min distance from any witness (in ORIGINAL time = q * cleared t) to any grid time a/8"""
    best=None
    for lo,hi in G:
        for w in (lo,hi,(lo+hi)/2):
            t=w*q                      # original time units
            x=(t*8)%1                  # position within an eighth
            d=min(x,1-x)/8             # distance to the nearest a/8 (any integer a)
            # only ODD a are grid times; nearest odd-a time:
            k=t*8
            import math
            cands=[F(math.floor(k))-1,F(math.floor(k)),F(math.floor(k))+1,F(math.floor(k))+2]
            dd=min(abs(t-F(c,8)) for c in cands if c%2==1)
            if best is None or dd<best: best=dd
    return best

BASE=[F(x) for x in (1,2,3,4,5,6,7,8)]
print("V = (s,2,3,4,5,6,7,8).  For each runner: distance from its nearest witness to the")
print("nearest GRID TIME a/8 (a odd), in ORIGINAL time units.  0 means 'at the usual place'.")
print()
print(f"  {'s':>7} {'period':>7}   " + " ".join(f"{'r'+str(i+1):>9}" for i in range(8)))
for k in (0,1,2,3,4,6,8,10,11):
    s=F(1)+F(k,12)
    V=[s]+BASE[1:]; E,q=clear(V)
    if len(set(E))<8: continue
    ds=[]
    for i in range(8):
        D=sorted({abs(w-E[i]) for w in E if w!=E[i]})
        G=bsm_good(D)
        ds.append(drift(G,q) if G else None)
    row=" ".join(f"{float(d):>9.5f}" if d is not None else f"{'--':>9}" for d in ds)
    print(f"  {str(s):>7} {q:>7}   {row}")
print()
print("  0.00000 = the witness sits exactly on a grid time. Nonzero = it has moved off.")
