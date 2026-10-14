"""The dichotomy:  either a flank in B is clear, or the resonant part A/n is itself 'easy'.
Large randomised hunt for B-failures, then characterise them."""
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
random.seed(99)
found=[]; scanned=0
for H in (20,28,40,56,80):
    got=0; tries=0
    while got<40000 and tries<3000000:
        tries+=1
        L=sorted(random.sample(range(1,H+1),7))
        if L[0]!=1: L[0]=1; L=sorted(set(L))
        if len(L)!=7 or not middle(L): continue
        got+=1; scanned+=1
        B=[d for d in L if d%N]
        if not any(any_clear(L,e) for e in B):
            A=[d for d in L if d%N==0]
            found.append((H,tuple(L),tuple(A),tuple(sorted(a//N for a in A))))
    print(f"  range [1,{H:3d}]: scanned {got}, B-failures so far {len(found)}")
print()
print(f"  TOTAL middle sets scanned: {scanned};  B-failures: {len(found)}")
print()
print("  every B-failure, with the reduced resonant part A/8:")
seen=set()
for H,L,A,Ared in found:
    print(f"    {L}   A={A}   A/8={Ared}   A/8 ratio-condition (max<=7*min)? {max(Ared)<=7*min(Ared)}")
    seen.add(Ared)
print()
print("  distinct A/8 among failures:",sorted(seen))
