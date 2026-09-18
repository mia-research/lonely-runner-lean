# A layered attack on door 4.  Each layer is a SUFFICIENT condition; measure what it covers
# and what is left, so the residue is explicit rather than vague.
from math import gcd
import random
n=8
def ok(ds,b,k):
    u=8*k+1
    return all(b <= (a*u)%(8*b) <= 7*b for a in ds)
def any_lonely(ds):
    return any(ok(ds,b,k) for b in ds for k in range(b))
L={ "L1 flank=1, k=0  (1 in ds, no a divisible by 8)":0,
    "L2 flank=min, k=0 (the bound)":0,
    "L3 any flank, k=0":0,
    "L4 any flank, k<b (full door 4)":0 }
res=[]; N=0
rng=random.Random(4)
for _ in range(20000):
    ds=sorted(rng.sample(range(1,80),7))
    g=gcd(*ds); ds=tuple(x//g for x in ds); N+=1
    m=min(ds)
    l1 = (1 in ds) and all(a%8!=0 for a in ds)
    l2 = ok(ds,m,0)
    l3 = any(ok(ds,b,0) for b in ds)
    l4 = any_lonely(ds)
    if l1: L["L1 flank=1, k=0  (1 in ds, no a divisible by 8)"]+=1
    if l2: L["L2 flank=min, k=0 (the bound)"]+=1
    if l3: L["L3 any flank, k=0"]+=1
    if l4: L["L4 any flank, k<b (full door 4)"]+=1
    if not l3 and l4: res.append(ds)
print(f"{N} primitive difference sets")
for k,v in L.items(): print(f"   {k:52s} {v:6d}  ({v/N:.3f})")
print(f"\n   sets needing k>0 somewhere (L3 fails, L4 holds): {len(res)} ({len(res)/N:.3f})")
print(f"   examples: {res[:4]}")
# how tight is it?  total lonely openings summed over flanks
tot=[]
rng=random.Random(11)
for _ in range(6000):
    ds=sorted(rng.sample(range(1,60),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    tot.append(sum(1 for b in ds for k in range(b) if ok(ds,b,k)))
tot.sort()
print(f"\n   total lonely openings per set: min {tot[0]}  1% {tot[len(tot)//100]}  median {tot[len(tot)//2]}")
print(f"   sets with exactly ONE lonely opening in the whole search: {tot.count(1)}")
