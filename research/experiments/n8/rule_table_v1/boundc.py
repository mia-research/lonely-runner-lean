# CANDIDATE RULE: there is always a lonely instant (8k+1)/(8c) with c <= C and k < c, for a
# small absolute C.  That would be a bounded, exhaustive naming rule.  Test hard.
from math import gcd
from itertools import combinations
import random
def ok(ds,c,k):
    u=8*k+1
    return all(c <= (a*u) % (8*c) <= 7*c for a in ds)
def smallest_c(ds, cmax=200):
    for c in range(1, cmax+1):
        for k in range(c):
            if ok(ds,c,k): return c,k
    return None
print("tight / named sets:")
for ds in [(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13),(2,3,4,5,6,7,16)]:
    print(f"   {str(ds):24s} -> {smallest_c(ds)}")
print()
for V in (14, 17):
    n=0; mx=None; hist={}
    for ds in combinations(range(1,V+1),7):
        if gcd(*ds)!=1: continue
        n+=1
        r=smallest_c(ds)
        if r is None:
            print(f"   NONE for {ds}"); continue
        hist[r[0]]=hist.get(r[0],0)+1
        if mx is None or r[0]>mx[0]: mx=(r[0],r[1],ds)
    print(f"[1,{V}] exhaustive, {n} sets: max smallest-c = {mx[0]} (k={mx[1]}) at {mx[2]}")
    print(f"        distribution of smallest c: {dict(sorted(hist.items()))}")
print()
rng=random.Random(4); mx=None; N=0; none=0
for _ in range(30000):
    ds=sorted(rng.sample(range(1,600),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    N+=1
    r=smallest_c(ds)
    if r is None: none+=1; continue
    if mx is None or r[0]>mx[0]: mx=(r[0],r[1],ds)
print(f"random up to 600: {N} sets, none found {none}, max smallest-c = {mx[0]} (k={mx[1]}) at {mx[2]}")
