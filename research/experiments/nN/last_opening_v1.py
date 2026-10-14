"""CLAIM: at the LAST opening j = e-1 of the flank e, disparity d is clear iff d >= e/(n-1).

Derivation: reading = d*(n(e-1)+1)/(n e) = d - d(n-1)/(n e), so
  circDist = circDist( d(n-1)/(n e) ),  which is >= 1/n  iff  1 <= d(n-1)/e <= n-1
  i.e.  e/(n-1) <= d <= e.
So if d_max <= (n-1) d_min -- the ratio condition -- the LAST opening is lonely, for every n.
That would explain the exhaustive finding of ZERO failures inside the ratio condition.
"""
import math
from itertools import combinations
from fractions import Fraction as F

def circDist(x):
    fr = x - math.floor(x); return min(fr, 1-fr)

def clear_at_last(d, e, n):
    t = (F(n*(e-1)+1))/(n*e)
    return circDist(F(d)*t) >= F(1,n)

print("=== claim: clear at j=e-1  iff  e/(n-1) <= d <= e ===")
bad = 0; tot = 0
for n in range(3, 13):
    for e in range(2, 60):
        for d in range(1, e+1):
            tot += 1
            pred = (F(e, n-1) <= d)
            act = clear_at_last(d, e, n)
            if pred != act:
                bad += 1
                if bad <= 8: print(f"   MISMATCH n={n} e={e} d={d}: predicted {pred}, actual {act}")
print(f"   checked {tot} (n,e,d) triples, mismatches: {bad}")
print()

print("=== consequence: inside the ratio condition, the last opening is lonely ===")
def works_at_last(c, n):
    e = c[-1]
    return all(clear_at_last(d, e, n) for d in c)
for n, hi in [(5,30),(6,24),(7,20),(8,16)]:
    k = n-1
    inside = tot = ok = 0
    for c in combinations(range(1,hi+1), k):
        g = c[0]
        for x in c[1:]: g = math.gcd(g,x)
        if g != 1: continue
        tot += 1
        if c[-1] * 1 <= (n-1)*c[0]:      # d_max <= (n-1) d_min
            inside += 1
            if works_at_last(c, n): ok += 1
    print(f"  n={n} [1,{hi}]: {inside} sets inside the ratio condition; last opening lonely for {ok} of them"
          f"   {'ALL' if ok == inside else '*** NOT ALL ***'}")
