"""RANGE SENSITIVITY.  The project's own 53/462 retraction was a figure exhaustive to 40 that
was not a floor beyond it.  Randomly sampled (never lexicographic), middle-of-trichotomy only."""
import random
from math import gcd
from itertools import combinations
N=8
def bset(d,e,n=N): return frozenset(j for j in range(e) if not (e<=(d*(n*j+1))%(n*e)<=(n-1)*e))
def bnds(ds,e,n=N):
    B=[bset(d,e,n) for d in ds if d!=e]
    if not B: return 0,0,0,0
    u=len(set().union(*B)); b0=sum(map(len,B))
    b1=min(len(B[i])+sum(len(B[k])-len(B[k]&B[i]) for k in range(len(B)) if k!=i) for i in range(len(B)))
    b2=b1
    for i in range(len(B)):
        for j in range(i+1,len(B)):
            base=len(B[i])+len(B[j])-len(B[i]&B[j])
            rest=sum(len(B[k])-max(len(B[k]&B[i]),len(B[k]&B[j])) for k in range(len(B)) if k not in (i,j))
            b2=min(b2,base+rest)
    return b0,b1,b2,u
def middle(L):
    M=sum(1 for d in L if d%N==0); return 1<=M<=len(L)-2

random.seed(20260922)
print("  range   sampled   union<e   pivot<e   2pivot<e   truth<e   2pivot MISSES   unsound")
for H in (21,30,40,60,80,120):
    got=0; c0=c1=c2=ct=0; bad=0; tries=0
    while got<1500 and tries<200000:
        tries+=1
        L=sorted(random.sample(range(1,H+1),7))
        if L[0]!=1: L[0]=1; L=sorted(set(L))
        if len(L)!=7 or not middle(L): continue
        got+=1
        r=[(e,)+bnds(L,e) for e in L]
        for e,b0,b1,b2,u in r:
            if b2<u: bad+=1
        c0+=any(b0<e for e,b0,b1,b2,u in r); c1+=any(b1<e for e,b0,b1,b2,u in r)
        c2+=any(b2<e for e,b0,b1,b2,u in r); ct+=any(u<e for e,b0,b1,b2,u in r)
    print(f"  [1,{H:3d}] {got:8d} {c0:9d} {c1:9d} {c2:10d} {ct:9d} {ct-c2:14d} {bad:9d}")
