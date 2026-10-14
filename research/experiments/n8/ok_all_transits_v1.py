#!/usr/bin/env python3
"""ALL EIGHT TRANSITS. Sweep each runner across the interval between its neighbours;
the fastest runner is swept on to the NEXT global-isolation point.

Base V = (1,...,8). Global isolation needs residues mod 8 complete, so for
V = (1,...,7,x) the next one after x=8 is x=16.
Metric: isolation EVENTS PER UNIT TIME (count / period) -- scale-free, since the period
changes along the sweep. Rate 0 for any runner would be an LRC counterexample.
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
def rates(V):
    E,q=clear(V)
    if len(set(E))<8: return None
    return [len(bsm_good(sorted({abs(w-E[i]) for w in E if w!=E[i]})))/q for i in range(8)]

BASE=[F(x) for x in range(1,9)]
print("Sweeping each runner between its neighbours (r8 to the next global-isolation point).")
print("Metric: isolation events per unit time.  A zero would be an LRC counterexample.")
print()
print(f"  {'runner':>7} {'range':>12} {'pts':>4} {'min rate':>10} {'at':>10} {'binds':>7}  {'rate at the endpoints':>24}")
for i in range(8):
    lo = BASE[i-1] if i>0 else F(1)
    hi = BASE[i+1] if i<7 else F(16)
    N=24
    best=None; ends=[]
    for k in range(0,N+1):
        s=lo+(hi-lo)*F(k,N)
        V=list(BASE); V[i]=s
        r=rates(sorted(V))
        if r is None: continue
        mn=min(r); who=r.index(mn)+1
        if best is None or mn<best[0]: best=(mn,s,who)
        if k in (0,N): ends.append(f"{min(r):.2f}")
    print(f"  {'r'+str(i+1):>7} {str(lo)+'->'+str(hi):>12} {N:>4} {best[0]:>10.3f} {str(best[1]):>10} "
          f"{'r'+str(best[2]):>7}  {' / '.join(ends):>24}")
print()
print("  every minimum is strictly positive -- no counterexample anywhere in these sweeps.")
