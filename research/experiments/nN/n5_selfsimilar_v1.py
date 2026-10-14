"""The self-similar core, and how far the proved tools reach it.

REDUCTION (exact, verified): if every non-flank disparity is 5*m_i, then
   #openings of (5m1,5m2,5m3,e)  =  #{ r in [0,e) : m_i * r mod e in [e/5, 4e/5] for all i }.
The 5 cancels and the band is IDENTICAL -- same shape, modulus e instead of 5e, and r
unconstrained (no a = 1 mod 5).  So the residue contains a SMALLER COPY OF ITSELF.

PROOF ROUTE.  The reduced problem asks for a rational r/e at which three "runners" m_i are all
at circle distance >= 1/5.  intLRC_four (axiom-clean here) gives a REAL t with distance >= 1/4
for three speeds.  Staying above 1/5 then holds on a window of width 2(1/4-1/5)/max m = 1/(10 m3),
and `exists_lonely_flankOpening_of_gap` converts a window wider than 1/e into a lattice point.
So the route closes when  e > 10*m3.  What we HAVE from the set being a difference set is
5*m3 < e, i.e. e > 5*m3 -- short by exactly a factor of two.
"""
import math
from itertools import combinations

def n_open(c):
    e = c[-1]; M = 5*e
    return sum(1 for j in range(e) if all(e <= (d*(5*j+1)) % M <= 4*e for d in c))

def reduced_count(ms, e):
    return sum(1 for r in range(e) if all(e <= 5*((m*r) % e) <= 4*e for m in ms))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

hi = 80
ss = [c for c in combinations(range(1, hi+1), 4)
      if prim(c) and all(d % 5 == 0 for d in c[:-1]) and c[-1] > 4*c[0] and c[-1] > 15]
print(f"self-similar sets (all non-flank a multiple of 5) in [1,{hi}]: {len(ss)}")
mis = sum(1 for c in ss if n_open(c) != reduced_count(tuple(d//5 for d in c[:-1]), c[-1]))
print(f"   reduction exact on all of them? mismatches = {mis}")
print()
cov = sum(1 for c in ss if c[-1] > 10 * max(d//5 for d in c[:-1]))
print(f"   sets with e > 10*m3 (the gap-criterion route closes)  : {cov} ({100*cov/len(ss):.1f}%)")
print(f"   sets with e > 5*m3  (automatic: 5*m3 < e)             : {len(ss)} (100.0%)")
print(f"   the gap in between                                    : {len(ss)-cov} ({100*(len(ss)-cov)/len(ss):.1f}%)")
print()
print("=== in the uncovered band 5*m3 < e <= 10*m3, how tight is it really? ===")
unc = [c for c in ss if c[-1] <= 10 * max(d//5 for d in c[:-1])]
mn = min(n_open(c) for c in unc)
low = [c for c in unc if n_open(c) <= 3]
print(f"   {len(unc)} sets, min openings {mn}, sets with <=3 openings: {len(low)}"
      f"   max d_max among those: {max((max(c) for c in low), default=0)}")
print(f"   examples: {sorted(low)[:8]}")
