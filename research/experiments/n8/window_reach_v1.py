"""What does first-lap clearance settle?
Flank e is clear at A (A = 8k+1 > 0) if every OTHER difference d has e <= d*A <= 7e.
An admissible A exists iff  ceil(e/dmin') <= A <= floor(7e/dmax')  contains an A = 1 mod 8,
which needs 7*dmin' >= dmax' (the other differences within a factor 7)."""
from math import gcd, lcm
from functools import lru_cache, reduce
from itertools import combinations_with_replacement
import random
@lru_cache(maxsize=None)
def cls(a,q):
    M=8*q
    return frozenset(k for k in range(q) if (lambda r:min(r,M-r)<q)((a*(8*k+1))%M))
def shadowed(ds,e):
    qs=[e//gcd(d,e) for d in ds]; L=reduce(lcm,qs); cov=set()
    for d,q in zip(ds,qs):
        cov|={k for k in range(L) if k%q in cls((d//(e//q))%(8*q), q)}
    return len(cov)==L
def window_A(ds,e):
    """smallest admissible A = 1 mod 8 for flank e, or None"""
    o=[d for d in ds if d!=e] or list(ds)
    lo=-(-e//min(o)); hi=(7*e)//max(o)
    A=lo + ((1-lo)%8)
    return A if A<=hi and A>0 else None
random.seed(6)
print("coverage of first-lap clearance, over multisets of 7 positive differences (gcd 1)")
print("  range    any flank has a window    d_max has a window    max<=7min (earlier thm)")
for hi in (20,60,200,2000):
    a=b=c=0; n=20000
    for _ in range(n):
        ds=tuple(random.randint(1,hi) for _ in range(7))
        g=reduce(gcd,ds); ds=tuple(d//g for d in ds)
        fl=sorted(set(ds))
        if any(window_A(ds,e) for e in fl): a+=1
        if window_A(ds,max(fl)): b+=1
        if max(ds)<=7*min(ds): c+=1
    print(f"  +-{hi:<6d}   {100*a/n:6.2f}%                  {100*b/n:6.2f}%              {100*c/n:6.2f}%")
print("\nsoundness: every window ever found really does clear the flank")
bad=0; n=0
for _ in range(60000):
    ds=tuple(random.randint(1,120) for _ in range(7))
    g=reduce(gcd,ds); ds=tuple(d//g for d in ds)
    for e in set(ds):
        A=window_A(ds,e)
        if A is None: continue
        n+=1
        M=8*e
        if any(min((d*A)%M, M-(d*A)%M)<e for d in ds if d!=e): bad+=1
print(f"   {n} windows checked: {'ALL CLEAR' if bad==0 else f'FAILS {bad}'}")
print("\nthe extremal set (2,3,4,5,6,7,16):")
ds=(2,3,4,5,6,7,16)
for e in sorted(set(ds)):
    print(f"   e={e:3d}  window A = {window_A(ds,e)}   shadowed={shadowed(ds,e)}")
