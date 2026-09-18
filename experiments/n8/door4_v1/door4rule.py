# b = max(ds) is NOT the right flank: when some runner shares a large gcd with it, the
# progression a*k mod b is coarse and the count collapses.  But another flank is then good.
# Test deterministic flank RULES: does any of them always give a lonely opening?
from math import gcd
import random
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def count(ds,b): return sum(1 for k in range(b) if all(clear(a,b,k) for a in ds))
def maxgcd(ds,b): return max((gcd(a,b) for a in ds if a!=b), default=1)
RULES = {
 "R1 b = max(ds)":            lambda ds: max(ds),
 "R2 min largest gcd, tie->max b": lambda ds: min(ds, key=lambda b:(maxgcd(ds,b), -b)),
 "R3 max b/maxgcd":           lambda ds: max(ds, key=lambda b:(b/maxgcd(ds,b), b)),
 "R4 max b coprime to all":   lambda ds: max([b for b in ds if maxgcd(ds,b)==1] or [max(ds)]),
}
res={k:[] for k in RULES}; best=[]
rng=random.Random(101); N=0
for _ in range(20000):
    ds=sorted(rng.sample(range(1,90),7)); g0=gcd(*ds); ds=[x//g0 for x in ds]
    if max(ds)<8: continue
    N+=1
    for name,f in RULES.items():
        res[name].append(count(ds,f(ds)))
    best.append(max(count(ds,b) for b in ds))
print(f"{N} primitive difference sets")
for name in RULES:
    v=sorted(res[name])
    print(f"  {name:30s} min {v[0]:3d}  1% {v[len(v)//100]:3d}  median {v[len(v)//2]:3d}   ZERO in {v.count(0)} sets")
bv=sorted(best)
print(f"  {'best over all flanks':30s} min {bv[0]:3d}  1% {bv[len(bv)//100]:3d}  median {bv[len(bv)//2]:3d}   ZERO in {bv.count(0)} sets")
print()
print("the three tight sets and the named hard arrangements, under each rule:")
for ds in [(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13),
           (49,205,234,256,286,323,366),(30,74,96,127,159,175,224)]:
    g0=gcd(*ds); d2=[x//g0 for x in ds]
    out={name: count(d2,f(d2)) for name,f in RULES.items()}
    print(f"   {str(ds):34s} {out}  best {max(count(d2,b) for b in d2)}")
