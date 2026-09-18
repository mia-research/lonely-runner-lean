# ExistenceAt8 asks for a lonely INSTANT, so the denominator c in t = 1/(8c) need NOT be in ds.
# t = 1/(8c) is lonely  iff  a mod 8c in [c, 7c] for every a in ds.
# c = 1 is the 'no a divisible by 8' theorem.  How far does free c reach?
from math import gcd
from itertools import combinations
import random
def ok(ds,c): return all(c <= (a % (8*c)) <= 7*c for a in ds)
def smallest_c(ds, cap=4000):
    for c in range(1, cap+1):
        if ok(ds,c): return c
    return None
rng=random.Random(5); cs=[]; none=0; N=0
for _ in range(20000):
    ds=sorted(rng.sample(range(1,300),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    N+=1
    c=smallest_c(ds)
    if c is None: none+=1
    else: cs.append(c)
cs.sort()
print(f"{N} primitive sets;  no c <= 4000 found: {none}")
print(f"  smallest working c : min {cs[0]}  median {cs[len(cs)//2]}  90th {cs[int(.9*len(cs))]}  max {cs[-1]}")
print(f"  c=1 works (no a divisible by 8): {cs.count(1)/len(cs):.4f}")
for B in (1,2,3,5,10,50,200):
    print(f"  smallest c <= {B:4d}: {sum(1 for x in cs if x<=B)/len(cs):.4f}")
print()
print("exhaustive [1,14], and the named hard sets:")
worst=None; n=0
for ds in combinations(range(1,15),7):
    if gcd(*ds)!=1: continue
    n+=1
    c=smallest_c(ds)
    if worst is None or (c is not None and c>worst[0]): worst=(c,ds)
print(f"   {n} sets, largest smallest-c = {worst[0]} at ds={worst[1]}")
for ds in [(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13),(2,3,4,5,6,7,16)]:
    print(f"   {str(ds):24s} smallest c = {smallest_c(ds)}")
