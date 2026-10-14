# Push the hunt: how large can the smallest naming c get?  And is the driver the number of
# differences divisible by 8 (or higher powers of 2)?
from math import gcd
import random
def ok(ds,c,k):
    u=8*k+1
    return all(c <= (a*u) % (8*c) <= 7*c for a in ds)
def smallest_c(ds, cmax=2000):
    for c in range(1, cmax+1):
        for k in range(c):
            if ok(ds,c,k): return c
    return None
def norm(ds):
    ds=tuple(sorted(set(ds)))
    if len(ds)!=7 or ds[0]<1: return None
    g=0
    for x in ds: g=gcd(g,x)
    return tuple(x//g for x in ds)
rng=random.Random(77); best=None
for restart in range(400):
    cur=norm(rng.sample(range(1,400),7))
    while cur is None: cur=norm(rng.sample(range(1,400),7))
    cc=smallest_c(cur) or 0
    for _ in range(400):
        i=rng.randrange(7); d=rng.choice([-32,-16,-8,-4,-2,-1,1,2,4,8,16,32])
        cand=list(cur); cand[i]+=d
        if cand[i]<1 or cand[i]>5000: continue
        nd=norm(cand)
        if nd is None: continue
        nc=smallest_c(nd) or 0
        if nc>cc: cur,cc=nd,nc
    if best is None or cc>best[0]: best=(cc,cur)
c,ds=best
print(f"hunt: max smallest-c = {c} at ds={ds}")
print(f"   divisible by 8 : {[a for a in ds if a%8==0]}  ({sum(1 for a in ds if a%8==0)} of 7)")
print(f"   2-adic valuations: {[(a & -a).bit_length()-1 for a in ds]}")
print()
# does #divisible-by-8 drive the required c?
from collections import defaultdict
buck=defaultdict(list)
rng2=random.Random(5)
for _ in range(12000):
    ds=norm(rng2.sample(range(1,400),7))
    if ds is None: continue
    c=smallest_c(ds, 400)
    if c is None: continue
    buck[sum(1 for a in ds if a%8==0)].append(c)
print(f"{'#div by 8':>10} {'n':>6} {'median c':>9} {'max c':>7}")
for k in sorted(buck):
    v=sorted(buck[k])
    if len(v)<15: continue
    print(f"{k:>10} {len(v):>6} {v[len(v)//2]:>9} {v[-1]:>7}")
