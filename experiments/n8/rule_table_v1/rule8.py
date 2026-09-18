# Does the triple of the three LARGEST flanks (ranks 4,5,6) always contain a working flank?
# Exhaustive on wider ranges, plus the tight sets and a spread-biased search.
from math import gcd
from itertools import combinations
import random
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def works(ds,b):
    for k in range(b):
        if all(clear(a,b,k) for a in ds): return True
    return False
def triple_ok(ds):
    s=sorted(ds)
    return works(ds,s[6]) or works(ds,s[5]) or works(ds,s[4])
for V in (17, 20, 22):
    n=0; bad=[]
    for ds in combinations(range(1,V+1),7):
        if gcd(*ds)!=1: continue
        n+=1
        if not triple_ok(ds): bad.append(ds)
    print(f"[1,{V}] exhaustive: {n} primitive sets, triple (4,5,6) FAILS on {len(bad)}")
    if bad: print(f"    {bad[:5]}")
print()
print("tight configurations:")
for ds in [(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]:
    s=sorted(ds)
    print(f"   {str(ds):24s} ranks 4,5,6 = {s[4]},{s[5]},{s[6]}  ->  {[works(ds,s[i]) for i in (4,5,6)]}")
print()
rng=random.Random(5); bad2=0; n2=0
for _ in range(40000):
    lo=rng.randrange(1,40)
    ds=sorted({lo}|set(rng.sample(range(lo+1,lo+500),6)))
    if len(ds)!=7: continue
    g=0
    for x in ds: g=gcd(g,x)
    ds=tuple(x//g for x in ds)
    if len(set(ds))!=7: continue
    n2+=1
    if not triple_ok(ds): bad2+=1
print(f"spread-biased sample: {n2} sets, triple fails on {bad2}")
