"""Two families of witness, and whether they are complementary.

FLANK   : t = (j + 1/5)/e -- denominator tied to a disparity.  The six criteria P1'..P7.
RATIONAL: t = a/q with q small -- denominator tied to nothing.  New.

Reported as COUNTS, not shares: the shares are enumeration artefacts (v19's reach withdrawal).
"""
from fractions import Fraction as F
from itertools import combinations
import math
n = 5
def min_q(ds, Q=40):
    for q in range(2, Q+1):
        for a in range(1, q):
            if math.gcd(a,q) != 1: continue
            ok = True
            for d in ds:
                r = (d*a) % q
                if not (F(1,n) <= min(F(r,q), 1 - F(r,q))): ok = False; break
            if ok: return q
    return None
def flank_any(ds):                      # exhaustive over every flank, proved iff (flankWorks_iff)
    for e in ds:
        M = n*e
        for j in range(e):
            if all(e <= (d*(n*j+1)) % M <= (n-1)*e for d in ds): return True
    return False
print(f"{'range':>8} {'sets':>8} {'max min-q':>10} {'need q>19':>10} {'need q>19 AND no flank':>24}")
for HI in (20,30,40,50,60,70):
    tot=0; worst=0; big=0; both=0; arg=None
    for c in combinations(range(1,HI+1),4):
        g=c[0]
        for x in c[1:]: g=math.gcd(g,x)
        if g!=1: continue
        tot+=1
        q=min_q(c)
        if q is None or q>19:
            big+=1
            if not flank_any(c): both+=1
        if q and q>worst: worst,arg=q,c
    print(f"[1,{HI:>2}]  {tot:>8} {worst:>10} {big:>10} {both:>24}   worst at {arg}")
