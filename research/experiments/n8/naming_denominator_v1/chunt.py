# How large can the general naming denominator c get?  Hunt to MAXIMISE it, at several scales.
from math import gcd
import random
def ok(ds,c,k):
    u=8*k+1
    return all(c <= (a*u) % (8*c) <= 7*c for a in ds)
def smallest_c(ds, cmax=3000):
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
overall=None
for scale,restarts in ((200,150),(2000,150),(20000,150)):
    rng=random.Random(scale); best=None
    for _ in range(restarts):
        cur=norm(rng.sample(range(1,scale),7))
        while cur is None: cur=norm(rng.sample(range(1,scale),7))
        cc=smallest_c(cur) or 0
        for _ in range(300):
            i=rng.randrange(7)
            d=rng.choice([-64,-32,-16,-8,-4,-2,-1,1,2,4,8,16,32,64])
            cand=list(cur); cand[i]+=d
            if cand[i]<1 or cand[i]>scale*4: continue
            nd=norm(cand)
            if nd is None: continue
            nc=smallest_c(nd) or 0
            if nc>cc: cur,cc=nd,nc
        if best is None or cc>best[0]: best=(cc,cur)
    print(f"  scale {scale:6d}: hunt max smallest-c = {best[0]:3d}  at {best[1]}")
    if overall is None or best[0]>overall[0]: overall=best
print()
print(f"OVERALL hunted maximum: c = {overall[0]} at ds={overall[1]}")
print(f"   its k: ", end="")
c=overall[0]
print([k for k in range(c) if ok(overall[1],c,k)][:5])
