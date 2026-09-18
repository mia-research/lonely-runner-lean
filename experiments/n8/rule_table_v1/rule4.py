# R1 = "use the nearest flank m".  Its condition is: some k < m is clear.  When m = 1 that is
# exactly "no difference = 0 mod 8".  When R1 fails, which flank serves?  Build R2.
from math import gcd
from itertools import combinations
import random
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def firstk(ds,b):
    for k in range(b):
        if all(clear(a,b,k) for a in ds): return k
    return None
def works(ds,b): return firstk(ds,b) is not None
# confirm the m=1 condition is exactly 'no difference divisible by 8'
rng=random.Random(4); ok=0; tot=0
for _ in range(20000):
    ds=sorted(rng.sample(range(2,90),6)); ds=tuple([1]+ds); g=gcd(*ds); ds=tuple(x//g for x in ds)
    if min(ds)!=1: continue
    tot+=1
    pred = all(a%8!=0 for a in ds)
    if works(ds,1)==pred: ok+=1
print(f"[1] m=1: 'nearest flank works' == 'no difference divisible by 8'  : {ok}/{tot} agree")
print()
# when R1 fails, which flank works?  test candidate rules among the REMAINING flanks
CAND = {
 "second smallest": lambda ds: sorted(ds)[1],
 "largest":         lambda ds: max(ds),
 "most openings that works": None,
}
rng2=random.Random(17); n=0; res={k:0 for k in CAND if CAND[k]}; anyworks=0; none=0
examples=[]
for _ in range(40000):
    ds=sorted(rng2.sample(range(1,90),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    m=min(ds)
    if works(ds,m): continue
    n+=1
    for name,f in CAND.items():
        if f is None: continue
        if works(ds,f(ds)): res[name]+=1
    good=[b for b in ds if works(ds,b)]
    if good: anyworks+=1
    else:
        none+=1
        if len(examples)<4: examples.append(ds)
print(f"[2] sets where R1 (nearest flank) FAILS: {n}")
for name,c in res.items():
    print(f"    fallback '{name}': works on {c} ({c/n:.3f})")
print(f"    some flank works: {anyworks} ({anyworks/n:.3f});  NO flank works: {none}")
if examples: print(f"    sets with no working flank: {examples}")
print()
# exhaustive check of the two-rule table on [1,14]
cnt=0; covered=0; miss=[]
for ds in combinations(range(1,15),7):
    if gcd(*ds)!=1: continue
    cnt+=1
    m=min(ds)
    if works(ds,m) or works(ds,max(ds)): covered+=1
    else: miss.append(ds)
print(f"[3] exhaustive [1,14]: R1 (nearest) OR R2 (largest) covers {covered}/{cnt} ({covered/cnt:.4f})")
print(f"    uncovered: {len(miss)}  examples {miss[:5]}")
