#!/usr/bin/env python3
"""A CONSTRUCTIVE induction on the interval structure, not the measure.

G_k = {t : ||e_i t|| >= 1/n, i <= k} is a union of closed intervals.  Let l_k be its longest.
Adding speed e:  the good set of e is periodic with period 1/e, containing in each period one
good interval of length g = (n-2)/(n e).  An interval of length L contains a COMPLETE good
interval of e whenever L >= 1/e + g = (2n-2)/(n e).

So if  l_k >= (2n-2)/(n e_{k+1}),  then  l_{k+1} >= (n-2)/(n e_{k+1}).
Starting from l_1 = (n-2)/(n e_1), the induction closes iff

    e_{k+1} >= ((2n-2)/(n-2)) * e_k      for every k        [ = 7/3 at n=8 ]

which PROVES LRC(n) for that tuple, constructively.  Verify the lemma and the conclusion.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd
import random

def goodset(E,n):
    iv=[]
    for e in E:
        for k in range(0,e+1):
            lo,hi=max(F(n*k-1,n*e),F(0)),min(F(n*k+1,n*e),F(1))
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
def longest(G): return max((b-a for a,b in G), default=F(0))

n=8; RATIO=F(2*n-2,n-2)
print(f"n={n}: the growth ratio is (2n-2)/(n-2) = {RATIO} = {float(RATIO):.4f}")
print()
print("STEP LEMMA: l_k >= (2n-2)/(n e) implies the next good set has longest >= (n-2)/(n e)")
random.seed(9); bad=0; tested=0
for _ in range(3000):
    k=random.randint(1,6)
    E=sorted(random.sample(range(1,60),k)); e=random.randint(1,60)
    if e in E: continue
    G=goodset(E,n); l=longest(G)
    if l >= F(2*n-2, n*e):
        tested+=1
        l2=longest(goodset(E+[e],n))
        if l2 < F(n-2, n*e): bad+=1
print(f"   {tested} qualifying cases, lemma violated in {bad}   "
      f"{'PASS' if bad==0 else '*** FAIL ***'}")

print("\nCONCLUSION: tuples with e_{k+1} >= 7/3 * e_k  =>  LRC(8) holds, with a witness")
bad=0; tested=0; ex=[]
for _ in range(4000):
    e=[random.randint(1,4)]
    for _ in range(6):
        e.append(max(int(e[-1]*float(RATIO))+random.randint(0,3), e[-1]+1))
    E=tuple(e)
    if max(E)>4000: continue
    if not all(F(E[i+1],E[i])>=RATIO for i in range(6)): continue
    tested+=1
    G=goodset(list(E),n)
    if not G: bad+=1
    if len(ex)<3: ex.append((E,longest(G)))
print(f"   {tested} lacunary tuples: good set EMPTY in {bad}   "
      f"{'PASS -- all have witnesses' if bad==0 else '*** FAIL ***'}")
for E,l in ex: print(f"     e.g. {E}   longest good interval {l} = {float(l):.6g}")

print("\nCOVERAGE: how many Case-2 tuples in [1..18] satisfy the growth condition?")
c=0; tot=0
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1 or all(x%8 for x in E): continue
    tot+=1
    if all(F(E[i+1],E[i])>=RATIO for i in range(6)): c+=1
print(f"   {c}/{tot} = {100*c/tot:.3f}%  -- the condition is PROVED but narrow in a small box")
