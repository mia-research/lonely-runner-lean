#!/usr/bin/env python3
"""FIRST INDIVIDUAL ISOLATION TIME of every runner, by the Boundary Set Method,
as runner 1's speed permutes from 1 up to 2.

BSM (phi_law_paper_v2 §2.2): runner i's isolation predicate changes only at the times where
some pairwise distance equals exactly 1/8, i.e. t' = (8k+-1)/(8d) for d in its constraint set.
Collect those, evaluate at entry and exit of each cell, take the earliest cell on which the
predicate holds.  Times are reported in ORIGINAL units (cleared time x period).
"""
from fractions import Fraction as F
from functools import reduce
from math import gcd, lcm

def clear(V):
    q=reduce(lcm,[x.denominator for x in V]); E=[int(x*q) for x in V]
    g=reduce(gcd,E); return [e//g for e in E], q//g

def bsm_first(D):
    """earliest t' in [0,1] with ||d t'|| >= 1/8 for all d in D, via the boundary set"""
    B={F(0),F(1)}
    for d in D:
        for k in range(0,d+1):
            for s in (1,-1):
                t=F(8*k+s,8*d)
                if 0<=t<=1: B.add(t)
    Bs=sorted(B)
    def ok(t): return all(min((F(d)*t)%1,1-(F(d)*t)%1)>=F(1,8) for d in D)
    for i in range(len(Bs)):
        if ok(Bs[i]):                       # a boundary time itself can be the witness
            return Bs[i]
        if i+1<len(Bs):
            mid=(Bs[i]+Bs[i+1])/2
            if ok(mid): return Bs[i]        # predicate holds across the whole cell
    return None

BASE=[F(x) for x in (1,2,3,4,5,6,7,8)]
print("V = (s, 2,3,4,5,6,7,8).  FIRST individual isolation time of each runner,")
print("in ORIGINAL time units, by BSM.  '--' = never (no witness in a full period).")
print()
print(f"  {'s':>7} {'period':>7}  " + "  ".join(f"{'r'+str(i+1):>9}" for i in range(8)))
for k in range(0,12):
    s=F(1)+F(k,12)
    V=[s]+BASE[1:]
    E,q=clear(V)
    if len(set(E))<8: print(f"  {str(s):>7}   (degenerate)"); continue
    row=[]
    for i in range(8):
        D=sorted({abs(w-E[i]) for w in E if w!=E[i]})
        f=bsm_first(D)
        row.append(f*q if f is not None else None)
    cells="  ".join((f"{str(x):>9}" if x is not None else f"{'--':>9}") for x in row)
    print(f"  {str(s):>7} {q:>7}  {cells}")
print()
print("  at s=1 every runner is isolated at t=1/8 simultaneously -- that is the AP grid.")
print("  off it, r1's first isolation time is the one that moves.")
