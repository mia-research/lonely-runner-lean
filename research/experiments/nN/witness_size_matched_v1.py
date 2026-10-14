# The per-order sweep used DIFFERENT ranges (26/20/15/13) and different set counts, so the flat
# q across orders is not a matched comparison.  Match it: same range, same sample size, per order.
from fractions import Fraction as F
import random, math
def min_q(ds, n, Q=200):
    for q in range(2, Q+1):
        for a in range(1, q):
            if math.gcd(a,q) != 1: continue
            if all(F(1,n) <= min(F((d*a)%q,q), 1-F((d*a)%q,q)) for d in ds): return q
    return None
random.seed(3)
N = 12000
print(f"matched: {N} random primitive tuples per order, entries from [1,200]")
print(f"{'n':>3} {'disparities':>12} {'max min-q':>10} {'median':>7}   witness")
for n in (5,6,7,8,9,10):
    k = n-1; worst = 0; arg = None; qs = []
    got = 0
    while got < N:
        ds = tuple(sorted(random.sample(range(1,201), k)))
        g = ds[0]
        for x in ds[1:]: g = math.gcd(g,x)
        if g != 1: continue
        got += 1
        q = min_q(ds, n)
        if q is None: print("   none <=200 at", ds); continue
        qs.append(q)
        if q > worst: worst, arg = q, ds
    qs.sort()
    print(f"{n:>3} {k:>12} {worst:>10} {qs[len(qs)//2]:>7}   {arg}")
