#!/usr/bin/env python3
"""(A) Do residual runners' single orbits give TIGHT witnesses?
   (B) Owner's hypothesis: move the OUTER runner to higher grid points; the impact of each
       step should DECREASE with distance from the AP, because a faster runner has more
       opportunities to isolate."""
from fractions import Fraction as F
from math import gcd
import random
from collections import Counter

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
def cons(V,i): return tuple(sorted({abs(w-V[i]) for w in V if w!=V[i]}))
def residual(D): return not any(all(d%q for d in D) for q in range(2,9))
def Aset(D,m): return [a for a in range(1,m) if gcd(a,m)==1 and all(min((d*a)%m,m-(d*a)%m)*8>=m for d in D)]

print("(A) residual runners: is the single-orbit witness TIGHT (min distance exactly 1/8)?")
random.seed(3); tight=Counter(); n=0
while n<2500:
    D=tuple(sorted(random.sample(range(1,60),7)))
    if not residual(D): continue
    for m in range(2,200):
        a=Aset(D,m)
        if a:
            n+=1
            t=F(a[0],m)
            md=min(min((F(d)*t)%1,1-(F(d)*t)%1) for d in D)
            tight['exactly 1/8' if md==F(1,8) else ('within 10% of 1/8' if md<F(11,80) else 'looser')]+=1
            break
for k,v in tight.most_common(): print(f"      {k:>20}: {v:>5} ({100*v/n:5.2f}%)")
print(f"   -> residual witnesses are {'mostly TIGHT' if tight['exactly 1/8']>n/2 else 'NOT generally tight'}")
print()

print("(B) move the outer runner: V = (1,2,3,4,5,6,7,x), x = 8,9,...")
print(f"   {'x':>4} {'x-7':>4} {'residual runners':>17} {'min |G_i| over runners':>24} {'change':>10}")
prev=None
for x in list(range(8,41))+[50,60,80,120]:
    V=tuple(list(range(1,8))+[x])
    if len(set(V))<8: continue
    ms=[]; nres=0
    for i in range(8):
        D=cons(V,i); ms.append(meas(bsm_good(D)))
        if residual(D): nres+=1
    mn=min(ms)
    ch='' if prev is None else f'{float(mn-prev):+.6f}'
    print(f"   {x:>4} {x-7:>4} {nres:>17} {str(mn):>16} = {float(mn):.6f} {ch:>10}")
    prev=mn
