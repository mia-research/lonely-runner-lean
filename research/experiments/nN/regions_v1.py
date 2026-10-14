"""Coverage of the PROVABLE regions of FourClears at n=5, and what is left.

  R1 (ratio condition)   all blockers d >= e/(n-1) = e/4      -> last opening, PROVED
  R2 (small blockers)    all blockers d <  e/10               -> LRC(3 speeds) slack + gap criterion
       reason: intLRC_four gives t with ||d_i t|| >= 1/4; staying >= 1/5 holds on a window of
       length 2*(1/4-1/5)/d_max = 1/(10 d_max), which exceeds 1/e exactly when e > 10 d_max.
"""
import math
from itertools import combinations
from fractions import Fraction as F

def works(c, n=5):
    e = c[-1]; M = n*e
    return any(all(e <= (d*(n*j+1)) % M <= (n-1)*e for d in c) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

for hi in (40, 60):
    tot = r1 = r2 = both = neither = 0
    ex = []
    for c in combinations(range(1,hi+1), 4):
        if not prim(c): continue
        tot += 1
        e = c[-1]; bl = c[:-1]
        in1 = all(4*d >= e for d in bl)          # d >= e/4
        in2 = all(10*d < e for d in bl)          # d < e/10
        if in1: r1 += 1
        if in2: r2 += 1
        if in1 and in2: both += 1
        if not in1 and not in2:
            neither += 1
            if len(ex) < 4: ex.append(c)
    print(f"n=5 exhaustive primitive 4-subsets of [1,{hi}]: {tot} sets")
    print(f"   R1 ratio condition (all d >= e/4) : {r1:>8}  ({100*r1/tot:6.2f}%)   PROVED")
    print(f"   R2 small blockers  (all d <  e/10): {r2:>8}  ({100*r2/tot:6.2f}%)   provable via intLRC_four")
    print(f"   overlap R1 & R2                   : {both:>8}")
    print(f"   NEITHER (still owed)              : {neither:>8}  ({100*neither/tot:6.2f}%)")
    print(f"   examples still owed: {ex}")
    print()
