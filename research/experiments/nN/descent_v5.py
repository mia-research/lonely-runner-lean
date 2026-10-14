"""Test the two halves of the candidate dichotomy separately.
  H1  A/n NOT ratio-easy   =>  some flank in B is clear          (the useful half)
  H2  A/n ratio-easy       =>  some flank in A is clear          (the exceptional branch)
Targeted sampling into each regime, never lexicographic."""
from math import gcd
import random
N=8
def clear_at(ds,e,k,n=N):
    a=n*k+1
    return all(e<=(d*a)%(n*e)<=(n-1)*e for d in ds)
def any_clear(ds,e,n=N): return any(clear_at(ds,e,k,n) for k in range(e))
def middle(L,n=N):
    M=sum(1 for d in L if d%n==0); return 1<=M<=len(L)-2
def easy(S): return max(S)<=(N-1)*min(S)
random.seed(1234)
print("  regime                       range   sets    violations   example violation")
for H in (40,60,100,160):
    h1t=h1v=h2t=h2v=0; v1=v2=None; tries=0
    while (h1t<2500 or h2t<2500) and tries<3000000:
        tries+=1
        L=sorted(random.sample(range(1,H+1),7))
        if L[0]!=1: L[0]=1; L=sorted(set(L))
        if len(L)!=7 or not middle(L): continue
        A=[d for d in L if d%N==0]; B=[d for d in L if d%N]
        Ared=[a//N for a in A]
        if not easy(Ared):
            if h1t>=2500: continue
            h1t+=1
            if not any(any_clear(L,e) for e in B):
                h1v+=1
                if v1 is None: v1=tuple(L)
        else:
            if h2t>=2500: continue
            h2t+=1
            if not any(any_clear(L,e) for e in A):
                h2v+=1
                if v2 is None: v2=tuple(L)
    print(f"  H1  A/8 not ratio-easy       [1,{H:3d}] {h1t:6d} {h1v:12d}   {v1}")
    print(f"  H2  A/8 ratio-easy           [1,{H:3d}] {h2t:6d} {h2v:12d}   {v2}")
