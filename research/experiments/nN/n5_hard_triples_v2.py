"""Primitive triples with S < 3/10 -- fast exact version.

S = sup_t min_i ||m_i t||.  The function is piecewise linear; its local maxima sit either at a
peak of one term, t = (2k+1)/(2 m_i), or at a crossing of two terms, which happens when
(m_i +- m_j) t is an integer.  So the candidate set is
      { k/(2 m_i) }  u  { k/(m_i + m_j) }  u  { k/|m_i - m_j| },
all in [0, 1/2] by symmetry.  Exact rationals, no grid, no import.
"""
import math, sys
from itertools import combinations
from fractions import Fraction as F

def norm(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)

def sup_min(ms):
    dens = set()
    for m in ms: dens.add(2*m)
    for a, b in combinations(ms, 2):
        dens.add(a+b)
        if a != b: dens.add(abs(a-b))
    cands = set()
    for q in dens:
        if q == 0: continue
        for k in range(0, q//2 + 2):
            t = F(k, q)
            if 0 <= t <= F(1,2): cands.add(t)
    best = F(0)
    for t in cands:
        v = min(norm(F(m) * t) for m in ms)
        if v > best: best = v
    return best

# sanity against the known values
for ms, exp in (((1,2,3), F(1,4)), ((1,3,4), F(2,7)), ((1,2,6), F(2,7)), ((2,3,5), F(2,7))):
    got = sup_min(ms)
    print(f"   check {ms}: S = {got}  expected {exp}  {'OK' if got == exp else 'MISMATCH'}")
print()
def prim3(ms):
    return math.gcd(math.gcd(ms[0], ms[1]), ms[2]) == 1
for B in (12, 20, 30, 40):
    hard = [(ms, sup_min(ms)) for ms in combinations(range(1, B+1), 3)
            if prim3(ms) and sup_min(ms) < F(3,10)]
    print(f"primitive triples with entries <= {B:>2}:  {len(hard)} have S < 3/10")
    for ms, S in hard: print(f"      {str(ms):>14}  S = {S}")
