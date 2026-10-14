"""RANGE TEST FIRST.  Does 'some flank in B = {d : n never-divides d} is clear' survive scale?"""
from math import gcd
from itertools import combinations
import random
N=8
def clear_at(ds,e,k,n=N):
    a=n*k+1
    return all(e<=(d*a)%(n*e)<=(n-1)*e for d in ds)
def any_clear(ds,e,n=N): return any(clear_at(ds,e,k,n) for k in range(e))
def middle(L,n=N):
    M=sum(1 for d in L if d%n==0); return 1<=M<=len(L)-2

random.seed(4242)
print("  range   middle sets   NO clear flank in B   NO clear flank at all   B-failures as witnesses")
fails=[]
for H in (28,40,60,90,140,200):
    t=nb=nc=0; tries=0
    while t<1200 and tries<400000:
        tries+=1
        L=sorted(random.sample(range(1,H+1),7))
        if L[0]!=1: L[0]=1; L=sorted(set(L))
        if len(L)!=7 or not middle(L): continue
        t+=1
        B=[d for d in L if d%N]
        okB=any(any_clear(L,e) for e in B)
        okAll=okB or any(any_clear(L,e) for e in L if d%N==0 for d in [e])
        if not okB:
            nb+=1
            if len(fails)<6: fails.append((H,tuple(L)))
        if not any(any_clear(L,e) for e in L): nc+=1
    print(f"  [1,{H:3d}] {t:12d} {nb:21d} {nc:23d}")
print()
print("  B-failure witnesses:")
for h,L in fails: print(f"    range {h}: {L}   A={[d for d in L if d%N==0]}")
