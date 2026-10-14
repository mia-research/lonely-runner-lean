#!/usr/bin/env python3
"""Concrete arrangements the grid reasoning does NOT cover, with the exact reason."""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd

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
def LU(E,a): return (max(F(1-(e*a)%8,8*e) for e in E), min(F(7-(e*a)%8,8*e) for e in E))
def UC(E): return {1,3,5,7} <= {e%8 for e in E}
def kindex(e,r,eps):
    """which interval index k runner e uses at offset eps"""
    lo=F(1-r,8*e)
    # intervals [lo + k/e, lo + 3/(4e) + k/e]
    import math
    k=math.floor((eps-lo)*e)
    for kk in (k-1,k,k+1):
        a,b=lo+F(kk,e), lo+F(3,4*e)+F(kk,e)
        if a<=eps<=b: return kk
    return None
def Kmin(E):
    G=goodset(E); best=None
    for a in (1,3,5,7):
        p=F(a,8)
        for lo,hi in G:
            for eps in ({F(0)} if lo<=p<=hi else set()) | {lo-p,hi-p}:
                if not (lo<=p+eps<=hi): continue
                ks=[kindex(e,(e*a)%8,eps) for e in E]
                if any(k is None for k in ks): continue
                K=max(abs(k) for k in ks)
                if best is None or K<best: best=K
    return best

def report(E,label):
    print(f"\n{label}\n  E = {E}")
    print(f"  residues mod 8: {[e%8 for e in E]}   Unit-Complete: {UC(E)}   "
          f"multiple of 8: {[e for e in E if e%8==0]}")
    for a in (1,3,5,7):
        R=[(e*a)%8 for e in E]; L,U=LU(E,a)
        vac=sorted(set(range(1,8))-set(R))
        print(f"    a={a}: residues {R}  vacant {vac}  L={L} U={U}  "
              f"{'FIRES' if L<=U else 'fails'}")
    print(f"  K_min = {Kmin(E)}")

print("="*78)
report((1,3,5,7,8,11,13), "(A) UNIT-COMPLETE -- no first-order direction exists at any a")
print("  Why: {1,3,5,7} all occupied, so mult-by-a can never vacate residue 7 (or 1).")
print("  Residue 7 pins U=0; the multiple of 8 (r=0) pins L>0. L>U at every a.")

report((1,2,3,4,5,6,8), "(B) STEERABLE, but Claim 4's SPEED condition FAILS")
E=(1,2,3,4,5,6,8); e0=8
for a in (1,3,5,7):
    R=[(e*a)%8 for e in E]
    if 7 in R: continue
    badj=[(e,r,(7-r)*e0) for e,r in zip(E,R) if r!=0 and e>(7-r)*e0]
    print(f"    a={a}: speed condition e_j <= (7-r_j)*e0={e0}: "
          f"{'holds' if not badj else 'FAILS at '+str(badj)}")

report((1,3,5,7,8,11,18), "(C) ESCAPES K=1 -- needs K=2 (worst rho*e_max in [1..18])")

print("\n" + "="*78)
print("(D) HOW BAD DOES K GET?  K_min on tuples with large rho*e_max from bigger boxes")
for E in ((5,7,9,11,12,37,40),(2,8,10,14,42,73,110),(8,23,261,395,420,562,596),
          (3,5,7,9,27,48,70),(1,5,6,7,11,32,36)):
    print(f"  {str(E):>34}  Unit-Complete={str(UC(E)):>5}  K_min = {Kmin(E)}")
