from math import gcd
from functools import lru_cache, reduce
from itertools import combinations_with_replacement
from collections import Counter
import sys
@lru_cache(maxsize=None)
def bmask(d,e):
    M=8*e; m=0
    for k in range(e):
        r=(d*(8*k+1))%M
        if min(r,M-r)<e: m|=1<<k
    return m
def rank(ds):
    fl=sorted(set(ds), reverse=True)
    for i,e in enumerate(fl):
        full=(1<<e)-1; cov=0
        for d in ds:
            cov|=bmask(d,e)
            if cov==full: break
        if cov!=full: return i+1
    return 99
N=int(sys.argv[1]) if len(sys.argv)>1 else 26
hist=Counter(); worst=0; ex=[]; tot=0
for ds in combinations_with_replacement(range(1,N+1),7):
    if reduce(gcd,ds)!=1: continue
    tot+=1
    r=rank(ds); hist[r]+=1
    if r>worst: worst,ex=r,[ds]
    elif r==worst and len(ex)<15: ex.append(ds)
print(f"exhaustive, 7 positive differences from [1,{N}], gcd=1: {tot} multisets")
print(f"  rank of first clear flank from the large end: {dict(sorted(hist.items()))}")
print(f"  WORST rank = {worst};  no clear flank at all: {hist.get(99,0)}")
print(f"  worst-rank examples:")
for d in ex[:15]:
    fl=sorted(set(d),reverse=True)
    print(f"     {d}  flanks={fl}  first clear = {fl[worst-1]}")
