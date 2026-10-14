"""H1 under pressure:  A/n NOT ratio-easy  =>  some flank in B = {d : n never-divides d} is clear.
Large samples, wide ranges, and a hunt for any violation."""
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
random.seed(555)
print("  range    H1-regime sets   violations   also: B-failures of ANY kind")
grand=0; gv=0
for H in (100,160,260,400):
    t=v=bf=0; tries=0; wit=None
    while t<6000 and tries<4000000:
        tries+=1
        L=sorted(random.sample(range(1,H+1),7))
        if L[0]!=1: L[0]=1; L=sorted(set(L))
        if len(L)!=7 or not middle(L): continue
        A=[d for d in L if d%N==0]; B=[d for d in L if d%N]
        okB=any(any_clear(L,e) for e in B)
        if not okB:
            bf+=1
            okA=any(any_clear(L,e) for e in A)
            if wit is None: wit=(tuple(L),tuple(sorted(a//N for a in A)),easy(sorted(a//N for a in A)),okA)
        Ared=sorted(a//N for a in A)
        if easy(Ared): continue
        t+=1; grand+=1
        if not okB: v+=1; gv+=1
    print(f"  [1,{H:3d}] {t:16d} {v:12d}   {bf}")
    if wit: print(f"          B-failure witness: {wit[0]}  A/8={wit[1]}  ratio-easy={wit[2]}  flank in A clear={wit[3]}")
print()
print(f"  H1 total: {grand} sets in regime, {gv} violations")
