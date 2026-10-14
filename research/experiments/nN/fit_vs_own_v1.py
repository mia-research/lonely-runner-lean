"""Item 24 asks how the FIT feeds each runner's reading.  ap_fit_spread_v1.py measures whether a
runner has an instant of the FITTED progression 7r/(8S).  Sec 2.3's own next sentence says the
runner's instant is read at its OWN d_min.  Measure both, on the same sets."""
from fractions import Fraction as F
from math import gcd
from functools import reduce
from itertools import combinations
def G(V): return reduce(gcd,[b-a for a,b in combinations(V,2)])
def fits(V):
    V=sorted(V); S=V[-1]-V[0]; D=F(S,7)
    return all(abs(V[k]-(V[0]+k*D))<D for k in range(8))
def has_fitted_instant(V,v):
    V=sorted(V); S=V[-1]-V[0]; g=G(V); N=8*S
    ds=[abs(v-w) for w in V if w!=v]; rmax=(16*S)//(7*g)+2
    return any(all(N<=8*((7*e*r)%N)<=7*N for e in ds) for r in range(1,rmax,2))
def has_own_instant(V,v,cap=200000):
    """cascade at the runner's OWN d_min; halts iff the runner is lonely"""
    ds=sorted(abs(v-w) for w in V if w!=v); dm=min(ds)
    S=[F(d,dm) for d in ds]; R=F(1)
    for _ in range(cap):
        out=[]
        for s in S:
            r=(s*R)%8
            if r<1: out.append((F(1)-r)/s)
            elif r>7: out.append((F(9)-r)/s)
        if not out: return True
        R=R+max(out)
    return False
import random
random.seed(24)
print("  runners with NO instant of the fitted progression — do they have one at their own d_min?")
print("  set                              fits   missed-by-fit   of those, isolated at own d_min")
tot=miss=rescued=0
examples=[(1,31,75,97,128,160,176,225),(1,2,3,4,5,6,7,9),(1,3,5,9,12,14,16,18),(1,2,3,4,5,6,7,8),(1,2,3,4,5,6,7,100)]
for V in examples:
    V=sorted(V); f=fits(V)
    m=[v for v in V if not has_fitted_instant(V,v)]
    r=[v for v in m if has_own_instant(V,v)]
    print(f"  {str(V):33s} {str(f):6s} {str(m):15s} {len(r)}/{len(m)}")
print()
print("  sweep: random 8-subsets of [1,40], gcd 1")
for _ in range(500):
    V=sorted(random.sample(range(1,41),8))
    if G(V)!=1: continue
    tot+=1
    m=[v for v in V if not has_fitted_instant(V,v)]
    miss+=len(m)
    rescued+=sum(1 for v in m if has_own_instant(V,v))
print(f"    sets {tot};  runner-misses against the fitted progression: {miss}")
print(f"    of those, isolated at their own d_min: {rescued}  ({'ALL' if rescued==miss else 'NOT all'})")
