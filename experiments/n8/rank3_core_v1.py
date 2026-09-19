"""All rank-3 sets over [1,40]: is there a bounded core, with the two large elements free?"""
from math import gcd
from functools import lru_cache, reduce
from itertools import combinations_with_replacement
from collections import Counter
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
N=40
S=[ds for ds in combinations_with_replacement(range(1,N+1),7)
   if reduce(gcd,ds)==1 and rank(ds)==3]
print(f"all rank-3 multisets over [1,{N}]: {len(S)}")
print(f"  contains 7            : {sum(1 for d in S if 7 in d)}/{len(S)}")
print(f"  first clear flank     : {Counter(sorted(set(d),reverse=True)[2] for d in S).most_common()}")
print(f"  5 smallest elements   : {Counter(tuple(sorted(d)[:5]) for d in S).most_common()}")
print(f"  2 largest elements    : {Counter(tuple(sorted(d)[5:]) for d in S).most_common(10)}")
print(f"  max of the 5 smallest : {max(max(sorted(d)[:5]) for d in S)}")
print(f"\n  all 41:")
for d in S: print(f"     {d}")
