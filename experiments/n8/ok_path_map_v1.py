#!/usr/bin/env python3
"""MAP THE 1.x -- the continuous path from a grid configuration to a hard one.

Take G0 = (1,2,3,4,5,6,7), residues mod 8 complete -> global isolation, the grid.
Take E* = (2,6,7,8,10,13,14), the Case-2 extremum.
Walk E(s) = (1-s)G0 + s E* through fractional speeds, clear denominators (LRC is
dilation-invariant), and record |G| and whether a witness exists at every step.
"""
from fractions import Fraction as F
from functools import reduce
from math import gcd, lcm

def goodset(E):
    iv=[]
    for e in E:
        for k in range(0,e+1):
            lo,hi=max(F(8*k-1,8*e),F(0)),min(F(8*k+1,8*e),F(1))
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
    g=reduce(gcd,E); return tuple(e//g for e in E)

G0=[F(x) for x in (1,2,3,4,5,6,7)]
ES=[F(x) for x in (2,6,7,8,10,13,14)]
print(f"{'s':>6} {'speeds (fractional)':>44} {'|G|':>12} {'witness?':>9} {'res mod 8 complete?':>20}")
for j in range(0,21):
    s=F(j,20)
    V=[(1-s)*a+s*b for a,b in zip(G0,ES)]
    E=clear(V)
    if max(E)>2500: print(f"{str(s):>6} {'(cleared tuple too large to evaluate)':>44}"); continue
    G=goodset(E); M=sum(b-a for a,b in G)
    R=sorted([0]+[e%8 for e in E])
    print(f"{str(s):>6} {str([str(v) for v in V]):>44}"[:52]
          + f" {float(M):>12.6f} {str(len(G)>0):>9} {str(R==list(range(8))):>20}")
