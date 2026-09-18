# Is the smallest naming c BOUNDED?  Max grew 9 -> 13 from [1,14] to [1,17].  Exhaustive wider,
# plus a hunt that maximises c directly.
from math import gcd
from itertools import combinations
import random
def ok(ds,c,k):
    u=8*k+1
    return all(c <= (a*u) % (8*c) <= 7*c for a in ds)
def smallest_c(ds, cmax=400):
    for c in range(1, cmax+1):
        for k in range(c):
            if ok(ds,c,k): return c
    return None
for V in (20, 22):
    n=0; mx=None
    for ds in combinations(range(1,V+1),7):
        if gcd(*ds)!=1: continue
        n+=1
        c=smallest_c(ds)
        if c is None: print(f"  NONE for {ds}"); continue
        if mx is None or c>mx[0]: mx=(c,ds)
    print(f"[1,{V}] exhaustive {n} sets: max smallest-c = {mx[0]} at {mx[1]}")
# targeted hunt: hill-climb to MAXIMISE the smallest c
rng=random.Random(2024); best=None
def norm(ds):
    ds=tuple(sorted(set(ds)))
    if len(ds)!=7 or ds[0]<1: return None
    g=0
    for x in ds: g=gcd(g,x)
    return tuple(x//g for x in ds)
for restart in range(120):
    cur=norm(rng.sample(range(1,200),7))
    while cur is None: cur=norm(rng.sample(range(1,200),7))
    cc=smallest_c(cur) or 0
    for _ in range(250):
        i=rng.randrange(7); d=rng.choice([-16,-8,-4,-2,-1,1,2,4,8,16])
        cand=list(cur); cand[i]+=d
        if cand[i]<1 or cand[i]>2000: continue
        nd=norm(cand)
        if nd is None: continue
        nc=smallest_c(nd) or 0
        if nc>cc: cur,cc=nd,nc
    if best is None or cc>best[0]: best=(cc,cur)
print(f"hunt maximising c, 120 restarts x 250 steps: max smallest-c = {best[0]} at {best[1]}")
