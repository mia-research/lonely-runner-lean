"""Existence at order 8 <=> every subject has a CLEAR FLANK.
A flank e is clear iff some opening k has no difference in the way.  Since every reduced
denominator q_j = e/gcd(|d_j|,e) divides e, the exact finite check runs over k in [0,e).
Question: can a subject have ALL SEVEN flanks shadowed?  Exhaustive over difference sets."""
from math import gcd, lcm
from itertools import combinations
from functools import lru_cache
import sys

@lru_cache(maxsize=None)
def blockmask(dm, e):
    """bitmask over k in [0,e) of openings where a mover with d = dm (mod 8e) is in the way"""
    M=8*e; m=0
    for k in range(e):
        r=(dm*(8*k+1))%M
        if min(r,M-r)<e: m|=1<<k
    return m

def clear_flanks(ds):
    """number of flanks e=|d| of this difference set that are clear at some opening"""
    c=0
    for e in sorted({abs(d) for d in ds}):
        full=(1<<e)-1; cov=0
        for d in ds:
            cov|=blockmask(d%(8*e), e)
            if cov==full: break
        if cov!=full: c+=1
    return c

N=int(sys.argv[1]) if len(sys.argv)>1 else 11
pool=[d for d in range(-N,N+1) if d!=0]
best=99; bestset=None; hist={}
tot=0
for ds in combinations(pool,7):
    tot+=1
    c=clear_flanks(ds)
    hist[c]=hist.get(c,0)+1
    if c<best: best,bestset=c,ds
print(f"exhaustive over 7-subsets of [-{N},{N}]\\{{0}}: {tot} difference sets")
print(f"  clear-flank count histogram: {dict(sorted(hist.items()))}")
print(f"  MINIMUM clear flanks = {best}   attained at ds = {bestset}")
