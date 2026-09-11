#!/usr/bin/env python3
"""GRID-ANCHORED WITNESS TRACKING (owner's idea).

Base = the grid times t=a/8, a in (Z/8)*, where the AP attains exact global isolation.
Deform: t = a/8 + eps.  A multiple of 8 leaves 0 at rate 8*delta; every other runner
leaves r/8 = (e a mod 8)/8 at rate e.  Question: is every witness reachable from a grid
point, and how far does the cover have to move?

Exact Fractions.  Gbar = closed good set {t : ||e t|| >= 1/8 for all e} (closed: the
blocked sets are OPEN), computed as the complement of the merged open bad set.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd
import random

def badset(E):
    iv=[]
    for e in E:
        for k in range(0,e+1):
            lo,hi=F(8*k-1,8*e),F(8*k+1,8*e)
            lo,hi=max(lo,F(0)),min(hi,F(1))
            if lo<hi: iv.append((lo,hi))
    iv.sort(); m=[]
    for lo,hi in iv:
        if m and lo<m[-1][1]: m[-1][1]=max(m[-1][1],hi)   # STRICT: open intervals touching leave a good point
        else: m.append([lo,hi])
    return m
def goodset(E):
    """closed complement; returns list of (lo,hi) with lo<=hi (lo==hi = isolated point)"""
    m=badset(E); g=[]; cur=F(0)
    for lo,hi in m:
        if cur<=lo: g.append((cur,lo))
        cur=max(cur,hi)
    if cur<=1: g.append((cur,F(1)))
    return [(a,b) for a,b in g if a<=b]
def dist_to_grid(E):
    """min over grid points a/8 of distance to the closed good set, exact"""
    G=goodset(E)
    best=None; arg=None
    for a in (1,3,5,7):
        p=F(a,8)
        for lo,hi in G:
            d = F(0) if lo<=p<=hi else min(abs(p-lo),abs(p-hi))
            # circular wrap
            d = min(d, abs(p-lo)%1, abs(p-hi)%1)
            if best is None or d<best: best,arg=d,(a,lo,hi)
    return best,arg
def res8(E): return {e%8 for e in E}
def unit_complete(E): return {1,3,5,7} <= res8(E)

PHI={2:1,3:2,4:2,5:4,6:2,7:6,8:4}
def case2(E): return any(e%8==0 for e in E)

print("CONTROL 1 -- Case 1 must have distance EXACTLY 0 (the grid point IS the witness)")
random.seed(11); bad=0; n=0
for _ in range(3000):
    E=tuple(sorted(random.sample(range(1,40),7)))
    if reduce(gcd,E)!=1 or case2(E): continue
    n+=1
    d,_=dist_to_grid(E)
    if d!=0: bad+=1
print(f"  {n} Case-1 tuples, nonzero distance in {bad}   {'PASS' if bad==0 else '*** FAIL ***'}")

print("\nCONTROL 2 -- the AP (1..7) is the grid: all 8 sites, gaps exactly 1/8")
pos=sorted({F(j,8) for j in range(8)})
print(f"  positions of (0,1..7) at t=1/8: {[str(F(j,8)) for j in range(8)]}")
print(f"  all gaps == 1/8: {all(pos[i+1]-pos[i]==F(1,8) for i in range(7))}")

print("\nTEST A -- does the first-order direction test predict Unit-Complete?")
print("  a direction survives at grid point a iff no runner has e*a = 7 mod 8 (eps>0)")
print("  or no runner has e*a = 1 mod 8 (eps<0).")
def firstorder_ok(E):
    for a in (1,3,5,7):
        R={(e*a)%8 for e in E}
        if 7 not in R or 1 not in R: return True
    return False
n=0; agree=0; tot=0
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1: continue
    tot+=1
    if firstorder_ok(E)==(not unit_complete(E)): agree+=1
print(f"  over {tot} primitive 7-tuples in [1..18]: first-order-fails <=> Unit-Complete"
      f" in {agree} ({100*agree/tot:.2f}%)   {'EXACT' if agree==tot else 'NOT exact'}")

print("\nTEST B -- how far must the cover move?  distance from grid to nearest witness")
R2=[E for E in combinations(range(1,19),7) if reduce(gcd,E)==1 and case2(E)]
from collections import Counter
hist=Counter(); worst=(F(0),None)
for E in R2:
    d,arg=dist_to_grid(E)
    hist[d==0]+=1
    if d>worst[0]: worst=(d,E,arg)
print(f"  Case-2 tuples [1..18]: {len(R2)}")
print(f"    distance 0 (grid point already a witness): {hist[True]}")
print(f"    distance > 0: {hist[False]}")
print(f"    MAX distance = {worst[0]} = {float(worst[0]):.6f}  at {worst[1]}")
print(f"    for comparison 1/8 = 0.125, and 1/(8*18) = {float(F(1,144)):.6f}")

print("\n" + "="*74)
print("TEST C -- is the 1/10 bound stable as the box grows?  (sampling missed an")
print("adversary once already, so adversaries are included)")
import sys
def sample(hi,N,pred):
    out=[]
    while len(out)<N:
        E=tuple(sorted(random.sample(range(1,hi+1),7)))
        g=reduce(gcd,E); E=tuple(e//g for e in E)
        if pred(E): out.append(E)
    return out
random.seed(3)
for hi,N in ((18,4000),(40,4000),(120,3000),(600,1500)):
    worst=(F(0),None)
    for E in sample(hi,N,lambda E: case2(E)):
        d,_=dist_to_grid(E)
        if d>worst[0]: worst=(d,E)
    print(f"  [1..{hi:<4d}] {N} Case-2: max grid distance {worst[0]} = {float(worst[0]):.6f}  at {worst[1]}")
# adversaries: Unit-Complete AND containing a multiple of 8, large speeds
worst=(F(0),None)
for _ in range(4000):
    base=[random.choice([8,16,24,32,40])]+[random.randrange(1,200) for _ in range(6)]
    E=tuple(sorted(set(base)))
    if len(E)!=7: continue
    g=reduce(gcd,E); E=tuple(e//g for e in E)
    if not (case2(E) and unit_complete(E)): continue
    d,_=dist_to_grid(E)
    if d>worst[0]: worst=(d,E)
print(f"  Unit-Complete + multiple of 8 adversaries: max {worst[0]} = {float(worst[0]):.6f}  at {worst[1]}")

print("\nTEST D -- is first-order OK a CERTIFICATE?  i.e. for non-Unit-Complete tuples,")
print("does a witness actually sit in the first-order-certified window?")
def certified_window_hit(E):
    emax=max(E)
    G=goodset(E)
    for a in (1,3,5,7):
        R={(e*a)%8 for e in E}
        for sgn in (1,-1):
            if (sgn==1 and 7 in R) or (sgn==-1 and 1 in R): continue
            p=F(a,8); w=F(1,8*emax)
            lo,hi=(p,p+w) if sgn==1 else (p-w,p)
            for gl,gh in G:
                if gl<=hi and lo<=gh: return True
    return False
n=0; hit=0
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1 or not case2(E) or unit_complete(E): continue
    n+=1
    if certified_window_hit(E): hit+=1
print(f"  non-Unit-Complete Case-2 tuples in [1..18]: {n}")
print(f"    witness inside the first-order window: {hit} ({100*hit/n:.2f}%)")
print(f"  -> first-order OK is {'a CERTIFICATE' if hit==n else 'NECESSARY but NOT SUFFICIENT'}")
