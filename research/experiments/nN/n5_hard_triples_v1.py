"""Is the set of PRIMITIVE triples with S <= 3/10 finite?

S(m1,m2,m3) = sup_t min_i ||m_i t||, computed EXACTLY on the vertex grid -- a finite decidable
calculation, no import.  S is scale-invariant: S(l*m) = S(m), since t -> t/l is a bijection of
the reals.  So only primitive triples matter.

The window route closes from the free bound e > 5*m3 exactly when S >= 3/10.  So the primitive
triples with S < 3/10 are the whole obstruction.  Scan them.
"""
import math
from itertools import combinations
from fractions import Fraction as F

def norm(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)

def sup_min(ms):
    dens = {2*m for m in ms}
    for a, b in combinations(ms, 2):
        dens.add(2*(a+b))
        if a != b: dens.add(2*abs(a-b))
    D = 1
    for d in dens: D = D * d // math.gcd(D, d)
    best = F(0)
    for k in range(D + 1):
        v = min(norm(F(m*k, D)) for m in ms)
        if v > best: best = v
            
    return best

def prim3(ms):
    return math.gcd(math.gcd(ms[0], ms[1]), ms[2]) == 1

for B in (12, 18, 25, 32):
    hard = []
    for ms in combinations(range(1, B+1), 3):
        if not prim3(ms): continue
        S = sup_min(ms)
        if S < F(3,10): hard.append((ms, S))
    print(f"primitive triples with entries <= {B:>2}: {len(hard)} have S < 3/10")
    for ms, S in hard: print(f"      {str(ms):>14}  S = {S}")
    print()
