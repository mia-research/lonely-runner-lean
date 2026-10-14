# Is the general naming denominator c BOUNDED as the speed bound V grows?  The dyadic route's
# kappa grew like log2 V and that closed it.  Measure general c over four doublings of V.
from math import gcd
import random, statistics
def ok(ds,c,k):
    u=8*k+1
    return all(c <= (a*u) % (8*c) <= 7*c for a in ds)
def smallest_c(ds, cmax=3000):
    for c in range(1, cmax+1):
        for k in range(c):
            if ok(ds,c,k): return c
    return None
print(f"{'V':>7} {'n':>6} {'median c':>9} {'90th':>6} {'max c':>6} {'none':>5}")
for V in (50, 200, 800, 3200, 12800, 50000):
    rng=random.Random(V); cs=[]; none=0; N=0
    trials = 3000 if V<=3200 else 1200
    for _ in range(trials):
        ds=sorted(rng.sample(range(1,V+1),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
        N+=1
        c=smallest_c(ds)
        if c is None: none+=1
        else: cs.append(c)
    cs.sort()
    print(f"{V:>7} {N:>6} {cs[len(cs)//2]:>9} {cs[int(.9*len(cs))]:>6} {cs[-1]:>6} {none:>5}")
print()
print("  for comparison the dyadic route's c = 2^(kappa-3) went 16, 32, 32, 64, 128 over V=50..800")
