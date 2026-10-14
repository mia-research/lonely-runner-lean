# The framework's own distinguished flank is the NEAREST runner m = min ds -- the bound, where
# the cascade starts.  Does flank b = m ALWAYS carry a lonely opening?  That would be the rule:
# "use the nearest flank", leaving only k to be named.
from math import gcd
from itertools import combinations
import random
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def N(ds,b): return sum(1 for k in range(b) if all(clear(a,b,k) for a in ds))
def firstk(ds,b):
    for k in range(b):
        if all(clear(a,b,k) for a in ds): return k
    return None
print("the three tight configurations:")
for ds in [(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]:
    m=min(ds); print(f"   {str(ds):24s} nearest flank {m}: count {N(ds,m)}  first k {firstk(ds,m)}")
print()
rng=random.Random(31); fails=[]; ks=[]; n=0
for _ in range(20000):
    ds=sorted(rng.sample(range(1,90),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    m=min(ds); n+=1
    k=firstk(ds,m)
    if k is None: fails.append(ds)
    else: ks.append(k)
print(f"random: {n} primitive sets, nearest flank has NO lonely opening in {len(fails)}")
if fails: print(f"   examples: {fails[:4]}")
if ks:
    ks.sort()
    print(f"   first k at the nearest flank: min {ks[0]}  median {ks[len(ks)//2]}  90th {ks[int(.9*len(ks))]}  max {ks[-1]}")
    print(f"   settled at k=0: {ks.count(0)/len(ks):.3f};  k<=2: {sum(1 for x in ks if x<=2)/len(ks):.3f}")
print()
# exhaustive on the small range where things are tight
bad=[]; cnt=0
for ds in combinations(range(1,15),7):
    if gcd(*ds)!=1: continue
    cnt+=1
    if firstk(ds,min(ds)) is None: bad.append(ds)
print(f"exhaustive over primitive 7-subsets of [1,14]: {cnt} sets, nearest flank fails on {len(bad)}")
if bad: print(f"   examples: {bad[:6]}")
