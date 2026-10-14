"""How much of FourClears do the framework's EXISTING band instances already settle?

`Flanks.clear_at_opening_of_band` says d is clear at flank e, opening k, when
    nM+1 <= (d/e)(nk+1) <= nM+n-1   for some integer M.
A whole set is settled at opening k when EVERY d has such an M.  Two named instances exist:
  k = 0,  M = 0        -> e <= d <= (n-1)e                       (Theorem 4.8's band)
  k = 1,  M = 0        -> e/(n+1) <= d <= (n-1)e/(n+1)           (clear_at_first_opening_of_ratio)
  k = e-1, M = d-1     -> e/(n-1) <= d <= e                      (clear_at_last_opening, new id)
Measure the coverage of each and of small-k unions, against the full set.
"""
import math
from itertools import combinations
from fractions import Fraction as F

def clear_at(d, e, n, k):
    """clear at flank e, opening k, by the band criterion (exact)."""
    v = F(d, e) * (n*k + 1)
    # need nM+1 <= v <= nM+n-1 for some integer M
    M = (v - 1) / n
    import math as _m
    for Mc in (_m.floor(M), _m.ceil(M)):
        if n*Mc + 1 <= v <= n*Mc + n - 1: return True
    return False

def settled_at(c, n, k):
    e = c[-1]
    return all(clear_at(d, e, n, k) for d in c)

def works(c, n):
    e = c[-1]; M = n*e
    return any(all(e <= (d*(n*j+1)) % M <= (n-1)*e for d in c) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

n = 5
for hi in (40, 60):
    tot = 0
    cov = {"k=e-1 (ratio cond)":0, "k=1":0, "k<=3":0, "k<=10":0, "k<=30":0, "any k<e":0}
    for c in combinations(range(1,hi+1), 4):
        if not prim(c): continue
        tot += 1
        e = c[-1]
        if settled_at(c, n, e-1): cov["k=e-1 (ratio cond)"] += 1
        if settled_at(c, n, 1): cov["k=1"] += 1
        if any(settled_at(c, n, k) for k in range(0, min(4, e))): cov["k<=3"] += 1
        if any(settled_at(c, n, k) for k in range(0, min(11, e))): cov["k<=10"] += 1
        if any(settled_at(c, n, k) for k in range(0, min(31, e))): cov["k<=30"] += 1
        if works(c, n): cov["any k<e"] += 1
    print(f"n=5, exhaustive primitive 4-subsets of [1,{hi}]: {tot} sets")
    for k, v in cov.items():
        print(f"   settled by {k:<22}: {v:>8}  ({100*v/tot:6.2f}%)")
    print()
