#!/usr/bin/env python3
"""Is the smallest witnessing denominator BOUNDED over the residual?

Residual = Case-2 tuples not closed by the small-denominator lemma, i.e. E hits every
d in 2..8 (SMALL_DENOMINATOR_WITNESS_v1 §4).  For each, find

   dmin(E) = min { d : some a with gcd(a,d)=1 has ||e a/d|| >= 1/8 for all e in E }

If dmin is bounded by a small D over the residual, n=8 outside Case 1 reduces to a finite
check over d <= D plus a proof of the bound.  Also measures Lemma 2 (the gcd form):
   d/gcd(e,d) in [2,8] for all e  =>  EVERY a works.
Exact Fraction on the decision path.
"""
from fractions import Fraction as F
from math import gcd
from itertools import combinations
from collections import Counter

def ok(E,d,a): return all(min((e*a)%d, d-(e*a)%d)*8 >= d for e in E)
def dmin(E,cap=400):
    for d in range(2,cap+1):
        for a in range(1,d):
            if gcd(a,d)==1 and ok(E,d,a): return d,a
    return None,None
def lemma2(E):
    for d in range(2,200):
        if all(2 <= d//gcd(e,d) <= 8 for e in E): return d
    return None
PHI={2:1,3:2,4:2,5:4,6:2,7:6,8:4}
def Nstar(E): return sum(p for d,p in PHI.items() if all(e%d for e in E))

res=[E for E in combinations(range(1,19),7)
     if gcd(*E)==1 and not all(e%8 for e in E) and Nstar(E)==0]
print(f"residual tuples in [1..18]: {len(res)}")
hist=Counter(); worst=(0,None); l2=0; fail=[]
for E in res:
    d,a=dmin(E)
    if d is None: fail.append(E); continue
    hist[d]+=1
    if d>worst[0]: worst=(d,E,a)
    if lemma2(E): l2+=1
print(f"  no witness with d<=400: {len(fail)}")
print(f"  Lemma 2 (gcd form, every a works) covers: {l2} ({100*l2/len(res):.2f}%)")
print(f"  MAX dmin over the whole residual: {worst[0]}   at {worst[1]}, a={worst[2]}")
print(f"  dmin distribution: {sorted(hist.items())}")
cum=0
for d,c in sorted(hist.items()):
    cum+=c
    print(f"    d<={d:3d}: {cum:5d}/{len(res)} = {100*cum/len(res):6.2f}%")
