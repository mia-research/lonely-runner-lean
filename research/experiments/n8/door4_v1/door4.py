# DOOR 4, exploration.  For integer ds and flank b in ds, an opening k in [0,b) is LONELY iff
#     b <= a*(8k+1) mod 8b <= 7b   for every a in ds.
# Questions: how many lonely openings per flank?  Is some flank always good?  Is there a RULE
# for which flank to pick?  Where is it tightest?
from itertools import combinations
from math import gcd
import random
n=8
def lonely_count(ds, b):
    c=0
    for k in range(b):
        u=8*k+1
        if all(b <= (a*u) % (8*b) <= 7*b for a in ds): c+=1
    return c
def profile(ds):
    return {b: lonely_count(ds,b) for b in ds}

print("=== the three tight sets, and the AP ===")
for ds in [(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]:
    p=profile(ds)
    best=max(p,key=lambda b:p[b])
    print(f"  {ds}:  per-flank lonely counts {p}")
    print(f"      best flank {best} with {p[best]} of {best} openings;  total lonely openings {sum(p.values())}")
print()
print("=== is the best flank ever the MINIMUM?  the MAXIMUM?  neither? ===")
rng=random.Random(9); stats={"min":0,"max":0,"other":0}; zero_total=0; N=0
worst=None
for _ in range(4000):
    ds=sorted(rng.sample(range(1,60),7))
    g=gcd(*ds); ds=tuple(x//g for x in ds)
    p=profile(ds); N+=1
    tot=sum(p.values())
    if tot==0: zero_total+=1
    bestb=max(p,key=lambda b:p[b])
    if bestb==min(ds): stats["min"]+=1
    elif bestb==max(ds): stats["max"]+=1
    else: stats["other"]+=1
    mx=max(p.values())
    if worst is None or mx<worst[0]: worst=(mx,ds,p)
print(f"  {N} sets: best flank is the smallest {stats['min']}, the largest {stats['max']}, neither {stats['other']}")
print(f"  sets with NO lonely opening at ANY flank: {zero_total}")
print(f"  hardest seen: max-over-flanks = {worst[0]}  at ds={worst[1]}")
print(f"      its profile {worst[2]}")
