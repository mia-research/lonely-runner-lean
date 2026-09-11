#!/usr/bin/env python3
"""TRANSIT MAP: move runner 1's speed continuously from its own value up to runner 2's,
and map the INDIVIDUAL ISOLATION set of EVERY runner throughout.

Rational speeds are cleared to integers (LRC is dilation-invariant), so the cleared time
variable runs over one full period -- important, because as two runners approach, the
period LENGTHENS and the witness moves far out in real time.
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
def meas(G): return sum(b-a for a,b in G)
def clear(V):
    q=reduce(lcm,[x.denominator for x in V]); E=[int(x*q) for x in V]
    g=reduce(gcd,E); return [e//g for e in E], q//g

BASE=[F(x) for x in (1,2,3,4,5,6,7,8)]
Q=12
print("V = (s, 2,3,4,5,6,7,8),  s running from 1 up to 2  (runner 1 transits to runner 2)")
print("|G_i| = fraction of the FULL period on which runner i is individually isolated.")
print()
hdr=" ".join(f"{v:>7}" for v in ('r1','r2','r3','r4','r5','r6','r7','r8'))
print(f"  {'s':>6} {'period':>7}  {hdr}   {'min':>8}  first witness of r1")
for k in range(0,Q):
    s=F(1)+F(k,Q)
    V=[s]+BASE[1:]
    E,q=clear(V)
    if len(set(E))<8: print(f"  {str(s):>6}   (degenerate: two runners share a speed)"); continue
    ms=[]; firsts=None
    for i in range(8):
        D=sorted({abs(w-E[i]) for w in E if w!=E[i]})
        G=bsm_good(D); ms.append(meas(G))
        if i==0: firsts = (G[0][0]*q if G else None)
    row=" ".join(f"{float(x):>7.4f}" for x in ms)
    print(f"  {str(s):>6} {q:>7}  {row}   {float(min(ms)):>8.4f}  t={firsts}")
print()
print("NOTE the period column: as s -> 2 the difference (2-s) shrinks, the cleared period")
print("grows, and runner 1's witness moves far out in real time even though the FRACTION")
print("of the period on which it is isolated stays bounded.")
