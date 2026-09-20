"""n=5 DoorLargestFlank: stress with the shapes that break it at 6, 7, 8.

The higher-order failures are small-consecutive runs: (1,3,4,5,6) at n=6, (1,2,3,5,7,10) at
n=7, (1,2,3,4,5,7,X) at n=8.  If n=5 survives the analogous families plus wide random ranges,
the n=5 result is not an artefact of the [1,80] window.
"""
import math, random
from fractions import Fraction as F
from itertools import combinations

INV = F(1,5)
def circDist(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)
def lonely(ds, t): return all(circDist(d*t) >= INV for d in ds)
def fo(e, j): return (F(j) + INV)/e
def fails(c):
    ds = [F(x) for x in c]; e = F(max(c))
    return not any(lonely(ds, fo(e, j)) for j in range(int(e)))

def run(name, sets):
    cnt, bad, ex = 0, 0, []
    for c in sets:
        c = tuple(sorted(set(c)))
        if len(c) != 4 or c[0] < 1: continue
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        cnt += 1
        if fails(c):
            bad += 1
            if len(ex) < 5: ex.append(c)
    print(f"  {name:<44} tested {cnt:>9}   FAILURES {bad}   {ex if ex else ''}")
    return bad

random.seed(5)
total = 0
# consecutive / near-consecutive small runs (the shape that breaks 6,7,8)
total += run("all 4-subsets of [1,12] (dense small runs)", combinations(range(1,13), 4))
# one large value against a small consecutive run
total += run("(a,a+1,a+2,X), a<=12, X<=4000",
             [(a, a+1, a+2, X) for a in range(1,13) for X in range(a+3, 4001)])
# two small, two large
total += run("(1,2,Y,Z) with Y<Z<=600", [(1,2,y,z) for y in range(3,600) for z in range(y+1,601)])
# arithmetic progressions
total += run("primitive APs a+di, a<=60, d<=60", [(a, a+d, a+2*d, a+3*d) for a in range(1,61) for d in range(1,61)])
# random wide
total += run("random 4-subsets of [1,20000], 400k draws",
             [tuple(random.sample(range(1,20001),4)) for _ in range(400000)])
# random with huge spread
total += run("random (small, large, large, large), 200k draws",
             [(random.randint(1,40), *sorted(random.sample(range(1000,10**7),3))) for _ in range(200000)])
print()
print(f"TOTAL FAILURES ACROSS ALL n=5 FAMILIES: {total}")
