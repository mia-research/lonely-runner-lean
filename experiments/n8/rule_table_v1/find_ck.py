# For the sets with no c at k=0, find the smallest (c,k) that names the instant.
# t = (8k+1)/(8c); by periodicity k < c suffices.  Condition: a(8k+1) mod 8c in [c,7c] for all a.
from math import gcd
import random
def ok(ds,c,k):
    u=8*k+1
    return all(c <= (a*u) % (8*c) <= 7*c for a in ds)
def k0_works(ds):
    m=min(ds)
    return any(ok(ds,c,0) for c in range(1,m+1))
def smallest_ck(ds, cmax=400):
    for c in range(1, cmax+1):
        for k in range(c):
            if ok(ds,c,k): return (c,k)
    return None
print("the named one-flank set:")
ds=(2,3,4,5,6,7,16)
print(f"   {ds}: k=0 works? {k0_works(ds)};  smallest (c,k) = {smallest_ck(ds)}")
print(f"      min(ds)={min(ds)}, elements divisible by 8: {[a for a in ds if a%8==0]}")
print()
rng=random.Random(9); fails=[]
while len(fails)<40:
    ds=sorted(rng.sample(range(1,300),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    if not k0_works(ds): fails.append(ds)
print(f"40 sets with no c at k=0 -- their smallest (c,k):")
rows=[]
for ds in fails:
    r=smallest_ck(ds)
    rows.append((ds,r))
for ds,r in rows[:12]:
    m=min(ds); bad=[a for a in ds if a%8==0]
    print(f"   {str(ds):34s} m={m:3d} div8={str(bad):12s} -> (c,k)={r}")
cs=[r[0] for _,r in rows if r]; ks=[r[1] for _,r in rows if r]
print()
print(f"   smallest c : min {min(cs)} median {sorted(cs)[len(cs)//2]} max {max(cs)};  none found: {sum(1 for _,r in rows if r is None)}")
print(f"   its k      : min {min(ks)} median {sorted(ks)[len(ks)//2]} max {max(ks)}")
print(f"   is c <= min(ds) ever? {sum(1 for (ds,r) in rows if r and r[0]<=min(ds))}/{len(rows)}")
print(f"   is c > min(ds)?       {sum(1 for (ds,r) in rows if r and r[0]>min(ds))}/{len(rows)}")
print(f"   is c in ds?           {sum(1 for (ds,r) in rows if r and r[0] in ds)}/{len(rows)}")
