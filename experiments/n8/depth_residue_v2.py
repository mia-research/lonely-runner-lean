"""Matched null for depth_residue_v1 (B),(C).  Depth is concentrated on small values, so 0.40
agreement may be nearly forced.  Same statistic on pairs with UNRELATED residues."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def cascade_full(v,i):
    t=TH/min(abs(v[j]-v[i]) for j in range(8) if j!=i); n=0; bl=set()
    while n<4000:
        b=[j for j in range(8) if j!=i and circd(F(abs(v[j]-v[i]))*t)<TH]
        if not b: return t,n,frozenset(bl)
        bl|=set(b); t=max(nextOp(F(abs(v[j]-v[i])),t) for j in b); n+=1
    return None,None,None
def build(rng,pi):
    q=[rng.randrange(0,7) for _ in range(8)]
    u=[pi[k]+8*q[k] for k in range(8)]
    if len(set(u))!=8 or gcd_all(u)!=1: return None
    return speeds([u[k]-min(u)+1 for k in range(8)]), sorted(range(8), key=lambda k: u[k])
def run(rng,matched,N=2000):
    ds=bs=tot=0; depths=Counter()
    trials=0
    while trials<N:
        piA=[rng.randrange(8) for _ in range(8)]
        piB=piA if matched else [rng.randrange(8) for _ in range(8)]
        A=build(rng,piA); B=build(rng,piB)
        if A is None or B is None: continue
        trials+=1
        (v,oA),(w,oB)=A,B
        pA={oA[p]:p for p in range(8)}; pB={oB[p]:p for p in range(8)}
        for tag in range(8):
            _,nA,blA=cascade_full(v,pA[tag]); _,nB,blB=cascade_full(w,pB[tag])
            if nA is None or nB is None: continue
            tot+=1; depths[nA]+=1
            if nA==nB: ds+=1
            if sorted((piA[oA[j]]-piA[tag])%8 for j in blA)==sorted((piB[oB[j]]-piB[tag])%8 for j in blB): bs+=1
    return ds/tot, bs/tot, tot, depths
d1,b1,tot,dep=run(random.Random(777),True)
d0,b0,_,_    =run(random.Random(5150),False)
print(f"                            depth same   blocker-offset-set same")
print(f"  MATCHED (same residues)     {d1:.4f}        {b1:.4f}")
print(f"  NULL    (unrelated)         {d0:.4f}        {b0:.4f}")
print(f"  n = {tot} subject-pairs")
print(f"\n  depth distribution: {dict(sorted(dep.items())[:8])}")
s=sum(dep.values()); import math
print(f"  forced floor (sum of squared depth freqs) = {sum((c/s)**2 for c in dep.values()):.4f}")
