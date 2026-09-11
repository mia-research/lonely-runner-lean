#!/usr/bin/env python3
"""HOW MANY TIMES does each runner isolate before the grand return?

For integer speeds with gcd 1 the whole configuration returns to the start at t = 1; for
rational speeds cleared to integers with period q, the grand return is at original t = q.
Count the maximal intervals (isolation EVENTS) of each runner's good set over one full
period. BSM good sets, exact Fraction.

GECT audit §7.2 records nu = phi(n) for the extremal runner -- check that first.
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

BASE=[F(x) for x in (1,2,3,4,5,6,7,8)]
print("ISOLATION EVENTS per runner, over one full period (up to the grand return).")
print("phi(8) = 4.")
print()
print(f"  {'s':>7} {'period':>7} {'grand return t':>15}  " + " ".join(f"{'r'+str(i+1):>5}" for i in range(8)) + "   total")
for k in range(0,12):
    s=F(1)+F(k,12)
    V=[s]+BASE[1:]; E,q=clear(V)
    if len(set(E))<8: continue
    ns=[]
    for i in range(8):
        D=sorted({abs(w-E[i]) for w in E if w!=E[i]})
        ns.append(len(bsm_good(D)))
    print(f"  {str(s):>7} {q:>7} {q:>15}  " + " ".join(f"{x:>5}" for x in ns) + f"   {sum(ns):>5}")
print()
print("  every count must be >= 1 -- a zero would be an LRC counterexample.")
print("  at s=1 the extremal runners r1, r8 should show phi(8) = 4.")
