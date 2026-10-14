#!/usr/bin/env python3
"""(1) Re-check the transit minima on a DENSE sample. The rate depends on the denominator
    of s (it sets the period), so sample every rational a/b with b <= B in range -- a
    uniform grid misses high-denominator points entirely.
   (2) Sweep the fastest runner between consecutive GLOBAL-ISOLATION points (x = 8 -> 16)
    and map the effect on every runner."""
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
def rates(V):
    E,q=clear(V)
    if len(set(E))<8: return None
    return [F(len(bsm_good(sorted({abs(w-E[i]) for w in E if w!=E[i]}))),q) for i in range(8)]

BASE=[F(x) for x in range(1,9)]
B=14
print(f"(1) DENSE re-check: every s = a/b in range with b <= {B}.  Old minima from 24 uniform points.")
print(f"  {'runner':>7} {'range':>10} {'points':>7} {'min rate':>10} {'at':>10} {'binder':>7} {'old (24 pts)':>13}")
old={0:2.208,1:2.0,2:2.0,3:2.0,4:2.0,5:2.0,6:2.0,7:2.750}
for i in range(8):
    lo = BASE[i-1] if i>0 else F(1)
    hi = BASE[i+1] if i<7 else F(16)
    seen=set(); best=None; n=0
    for b in range(1,B+1):
        a0=int(lo*b); a1=int(hi*b)+1
        for a in range(a0,a1+1):
            s=F(a,b)
            if not (lo<=s<=hi) or s in seen: continue
            seen.add(s)
            V=list(BASE); V[i]=s
            r=rates(sorted(V))
            if r is None: continue
            n+=1; mn=min(r); who=r.index(mn)+1
            if best is None or mn<best[0]: best=(mn,s,who)
    flag='' if abs(float(best[0])-old[i])<1e-9 else '  <-- LOWER'
    print(f"  {'r'+str(i+1):>7} {str(lo)+'->'+str(hi):>10} {n:>7} {str(best[0]):>10} {str(best[1]):>10} "
          f"{'r'+str(best[2]):>7} {old[i]:>13.3f}{flag}")
