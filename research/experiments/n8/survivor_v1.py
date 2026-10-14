"""WHICH flank survives when nearly all are shadowed, and WHY?
Candidate answers: (i) it is d_max; (ii) it is the flank with the largest L = lcm_j q_j.
In (2,3,4,5,6,7,16) these coincide -- so test whether they ever diverge."""
from math import gcd, lcm
from functools import lru_cache, reduce
from itertools import combinations_with_replacement
from collections import Counter
import sys
@lru_cache(maxsize=None)
def cls(a,q):
    M=8*q
    return frozenset(k for k in range(q) if (lambda r:min(r,M-r)<q)((a*(8*k+1))%M))
@lru_cache(maxsize=None)
def info(ds,e):
    qs=tuple(e//gcd(d,e) for d in ds); L=reduce(lcm,qs); cov=set()
    for d,q in zip(ds,qs):
        cov|={k for k in range(L) if k%q in cls((d//(e//q))%(8*q), q)}
    free=sorted(set(range(L))-cov)
    return L,(len(cov)==L),(free[0] if free else None)
print("anatomy of the extremal set (2,3,4,5,6,7,16):")
ds=(2,3,4,5,6,7,16)
for e in sorted(set(ds)):
    L,sh,k0=info(ds,e)
    qs=[e//gcd(d,e) for d in ds]
    print(f"   flank e={e:3d}  q_j={qs}  L={L:3d}  {'SHADOWED' if sh else f'CLEAR at k={k0}, t={8*k0+1}/{8*e}'}")
N=int(sys.argv[1]) if len(sys.argv)>1 else 20
isMax=Counter(); isMaxL=Counter(); n1=0; worst=0
for d in combinations_with_replacement(range(1,N+1),7):
    if reduce(gcd,d)!=1: continue
    fl=sorted(set(d)); res={e:info(d,e) for e in fl}
    clear=[e for e in fl if not res[e][1]]
    worst=max(worst,len(fl)-len(clear))
    if len(clear)==1:
        n1+=1
        c=clear[0]
        isMax[c==max(fl)]+=1
        mL=max(res[e][0] for e in fl)
        isMaxL[res[c][0]==mL]+=1
print(f"\nover [1,{N}]: max shadowed = {worst}; multisets with EXACTLY ONE clear flank: {n1}")
print(f"   the clear flank is d_max        : {isMax[True]} yes / {isMax[False]} no")
print(f"   the clear flank has the largest L: {isMaxL[True]} yes / {isMaxL[False]} no")
