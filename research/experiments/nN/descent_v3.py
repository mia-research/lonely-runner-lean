"""Find and characterise the exceptions to 'some flank in B is clear'."""
from math import gcd
from itertools import combinations
N=8
def clear_at(ds,e,k,n=N):
    a=n*k+1
    return all(e<=(d*a)%(n*e)<=(n-1)*e for d in ds)
def any_clear(ds,e,n=N): return any(clear_at(ds,e,k,n) for k in range(e))
def middle(L,n=N):
    M=sum(1 for d in L if d%n==0); return 1<=M<=len(L)-2
ex=[]; tot=0
for L in combinations(range(1,29),7):
    if L[0]!=1: continue
    L=list(L)
    if not middle(L): continue
    tot+=1
    B=[d for d in L if d%N]
    if not any(any_clear(L,e) for e in B):
        A=[d for d in L if d%N==0]
        good=[e for e in L if any_clear(L,e)]
        ex.append((tuple(L),A,B,good))
print(f"  middle sets in [1,28]: {tot}")
print(f"  exceptions to 'some flank in B is clear': {len(ex)}")
for L,A,B,good in ex:
    print(f"    {L}")
    print(f"       A (multiples of 8) = {A}")
    print(f"       B                  = {B}")
    print(f"       flanks that DO work = {good}")
    for e in good:
        ks=[k for k in range(e) if clear_at(list(L),e,k)]
        print(f"         e={e}: clear openings k = {ks[:12]}{'...' if len(ks)>12 else ''}")
