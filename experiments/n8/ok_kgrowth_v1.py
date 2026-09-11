#!/usr/bin/env python3
"""How far does K go?  K_min ~ rho(E)*e_max, and rho looked like C/sqrt(e_max),
so K should grow like sqrt(e_max) -- i.e. be UNBOUNDED.  Test, and exhibit witnesses."""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd, floor
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
def kindex(e,r,eps):
    lo=F(1-r,8*e); k=floor((eps-lo)*e)
    for kk in (k-1,k,k+1):
        if lo+F(kk,e) <= eps <= lo+F(3,4*e)+F(kk,e): return kk
    return None
def Kmin(E):
    G=goodset(E); best=None
    for a in (1,3,5,7):
        p=F(a,8)
        for lo,hi in G:
            cands={lo-p,hi-p} | ({F(0)} if lo<=p<=hi else set())
            for eps in cands:
                if not (lo<=p+eps<=hi): continue
                ks=[kindex(e,(e*a)%8,eps) for e in E]
                if any(k is None for k in ks): continue
                K=max(abs(k) for k in ks)
                if best is None or K<best: best=K
    return best
def LU(E,a): return (max(F(1-(e*a)%8,8*e) for e in E), min(F(7-(e*a)%8,8*e) for e in E))
def UC(E): return {1,3,5,7} <= {e%8 for e in E}

print("A genuine STEERABLE tuple (not Unit-Complete) whose principal certificate FAILS:")
found=[]
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1 or all(e%8 for e in E) or UC(E): continue
    if all(LU(E,a)[0] > LU(E,a)[1] for a in (1,3,5,7)):
        found.append(E)
        if len(found)==3: break
for E in found:
    print(f"  E = {E}   residues {[e%8 for e in E]}   K_min = {Kmin(E)}")
    a=next(a for a in (1,3,5,7) if 7 not in [(e*a)%8 for e in E])
    e0=min(e for e in E if e%8==0); R=[(e*a)%8 for e in E]
    viol=[(e,r,(7-r)*e0) for e,r in zip(E,R) if r!=0 and e>(7-r)*e0]
    print(f"    at a={a} (residue 7 vacant): speed condition e_j <= (7-r_j)*{e0} "
          f"violated by {viol}")

print("\nK_min GROWTH -- max over sampled tuples, by box")
random.seed(4)
for hi,N in ((18,6000),(60,4000),(200,2500),(800,1200),(3000,600)):
    best=(0,None); n=0
    while n<N:
        E=tuple(sorted(random.sample(range(1,hi+1),7)))
        g=reduce(gcd,E); E=tuple(e//g for e in E)
        if len(set(E))!=7 or all(e%8 for e in E): continue
        n+=1
        K=Kmin(E)
        if K and K>best[0]: best=(K,E)
    print(f"  [1..{hi:<5d}]  max K_min = {best[0]:>3}   at {best[1]}")
