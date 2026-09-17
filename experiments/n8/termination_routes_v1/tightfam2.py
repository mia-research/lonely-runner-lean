# CORRECTED.  max_t min_d ||d t|| is piecewise linear in t; its maximum is attained at a
# kink of some ||d t|| (t = k/(2d)) or where two of them cross ((d_i +- d_j) t in Z).
# Searching flank openings ONLY is wrong: there the flank runner sits at exactly 1/8 by
# construction, so the min is forced <= 1/8 and every set reports "tight".
from fractions import Fraction as F
from itertools import combinations
from math import gcd
n = 8
def circ(x):
    f = x - (x.numerator // x.denominator); return min(f, 1-f)
def best_min(ds):
    cands = set()
    for d in ds:
        for k in range(1, 2*d): cands.add(F(k, 2*d))
    for a, b in combinations(ds, 2):
        for s in (a+b, abs(a-b)):
            if s: 
                for k in range(1, s+1): cands.add(F(k, s))
    best = F(0)
    for t in cands:
        m = min(circ(F(d)*t) for d in ds)
        if m > best: best = m
    return best
# sanity: the AP {1..7} must come out exactly 1/8
ap = best_min((1,2,3,4,5,6,7))
print(f"sanity  {{1..7}} best min-distance = {ap} (must be 1/8 = {F(1,8)})  -> {'OK' if ap==F(1,8) else 'BROKEN'}")
for V in (10, 12, 14):
    tight, loose, below = [], 0, 0
    for ds in combinations(range(1, V+1), 7):
        if gcd(*ds) != 1: continue
        b = best_min(ds)
        if b < F(1,n): below += 1
        elif b == F(1,n): tight.append(ds)
        else: loose += 1
    print(f"V={V:2d}: primitive 7-subsets -> tight {len(tight)}, loose {loose}, below 1/8 {below}")
    for t in tight: print("      TIGHT", t)
