# How deep does door 4 actually need to go?  With the k=0 layer now pruned to the single
# nearest flank, the question is the SMALLEST k at which some flank is free.
from math import gcd
import random
def ok(ds,b,k):
    u=8*k+1
    return all(b <= (a*u)%(8*b) <= 7*b for a in ds)
def min_k(ds):
    for k in range(max(ds)):
        for b in ds:
            if k < b and ok(ds,b,k): return k
    return None
rng=random.Random(17); ks=[]; none=0
for _ in range(6000):
    ds=sorted(rng.sample(range(1,80),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    k=min_k(ds)
    if k is None: none+=1
    else: ks.append(k)
ks.sort()
print(f"{len(ks)} sets, no lonely opening found: {none}")
print(f"  smallest k that works: min {ks[0]}  median {ks[len(ks)//2]}  90th {ks[int(.9*len(ks))]}  max {ks[-1]}")
print(f"  fraction settled at k=0 : {ks.count(0)/len(ks):.3f}")
print(f"  fraction settled at k<=2: {sum(1 for k in ks if k<=2)/len(ks):.3f}")
print(f"  fraction settled at k<=8: {sum(1 for k in ks if k<=8)/len(ks):.3f}")
print()
print("the three tight sets and the named hard arrangements:")
for ds in [(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13),
           (49,205,234,256,286,323,366),(30,74,96,127,159,175,224)]:
    g=gcd(*ds); d2=tuple(x//g for x in ds)
    print(f"   {str(ds):34s} -> smallest k = {min_k(d2)}")
