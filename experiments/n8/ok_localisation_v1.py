#!/usr/bin/env python3
"""LOCALISATION: is every witness within 1/e_max of a grid point a/8?
rho(E) = exact distance from the nearest grid point to the closed good set.
Scale-free statistic: rho(E) * e_max.  If < 1 always, the witness lies inside one period
of the fastest runner, measured from the grid -- the localisation the LRC(7) route lacked."""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd
import random

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
def rho(E):
    G=goodset(E); best=None
    for a in (1,3,5,7):
        p=F(a,8)
        for lo,hi in G:
            d=F(0) if lo<=p<=hi else min(abs(p-lo),abs(p-hi))
            if best is None or d<best: best=d
    return best

print("EXHAUSTIVE over [1..18]: max of rho(E) * e_max on Case 2")
worst=(F(0),None); n=0; over=0
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1 or all(e%8 for e in E): continue
    n+=1
    v=rho(E)*max(E)
    if v>=1: over+=1
    if v>worst[0]: worst=(v,E,rho(E))
print(f"  {n} Case-2 tuples;  max rho*e_max = {worst[0]} = {float(worst[0]):.6f}  at {worst[1]}")
print(f"  (rho there = {worst[2]}, e_max = {max(worst[1])})")
print(f"  tuples with rho*e_max >= 1: {over}   -> conjecture {'HOLDS in box' if over==0 else 'FAILS'}")

print("\nSAMPLED at larger boxes, plus adversaries (sampling missed one before)")
random.seed(19)
def run(gen,lab,N):
    worst=(F(0),None); n=0
    while n<N:
        E=gen()
        if E is None: continue
        g=reduce(gcd,E); E=tuple(e//g for e in E)
        if len(set(E))!=7 or all(e%8 for e in E): continue
        n+=1
        v=rho(E)*max(E)
        if v>worst[0]: worst=(v,E)
    print(f"  {lab:<34} max rho*e_max = {float(worst[0]):.6f}  at {worst[1]}")
for hi,N in ((40,4000),(120,2000),(600,800)):
    run(lambda hi=hi: tuple(sorted(random.sample(range(1,hi+1),7))), f"random [1..{hi}]", N)
run(lambda: tuple(sorted(set([random.choice([8,16,24,32])]+random.sample(range(1,60),6)))) if True else None,
    "forced multiple of 8", 3000)
run(lambda: tuple(sorted(set([8*random.randint(1,9)]+[random.choice([1,3,5,7])+8*random.randint(0,7) for _ in range(4)]+random.sample(range(1,80),2)))),
    "Unit-Complete + multiple of 8", 3000)
