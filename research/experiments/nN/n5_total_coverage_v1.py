"""Total PROVED coverage at n = 5 after the whittling.

  P1'  no NON-FLANK disparity divisible by 5   -> Resonance.flankWorks_of_prime(_dvd)  [PROVED]
  P2   d_max <= 4*d_min                        -> FlankFinite.clear_at_last_opening    [PROVED]
  P3   d_max <= 15                             -> FlankFinite.four_clears_small        [PROVED, decide]
  P4   W > 1/e, W = largest interval of the lonely set of the NON-FLANK disparities
                                               -> FlankFinite.exists_lonely_flankOpening_of_gap
                                                  + an exact finite computation of W   [PROVED]
  P5   all non-flank divisible by 5, handled by the scaling reduction + window + finite check
                                               [closed modulo the five-triple statement]
"""
import math
from itertools import combinations
from fractions import Fraction as F

def norm(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)

def max_gap(ds, _c={}):
    key = tuple(ds)
    if key in _c: return _c[key]
    pts = {F(0), F(1)}
    for d in ds:
        for k in range(0, d + 2):
            for off in (F(-1,5), F(1,5)):
                t = (F(k) + off) / F(d)
                if 0 <= t <= 1: pts.add(t)
    P = sorted(pts); best = F(0)
    for i in range(len(P)-1):
        lo, hi = P[i], P[i+1]
        if all(norm(F(d)*((lo+hi)/2)) >= F(1,5) for d in ds) and hi-lo > best: best = hi-lo
    _c[key] = best
    return best

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

for hi in (30, 40):
    tot = 0
    cov = {k: 0 for k in ("P1'", "P2", "P3", "P4", "P5", "union")}
    rem = 0
    for c in combinations(range(1, hi+1), 4):
        if not prim(c): continue
        tot += 1
        e = c[-1]; nf = c[:-1]
        a = all(d % 5 != 0 for d in nf)
        b = e <= 4*c[0]
        d_ = e <= 15
        f = max_gap(nf) > F(1, e)
        g = all(d % 5 == 0 for d in nf)
        for k, v in (("P1'", a), ("P2", b), ("P3", d_), ("P4", f), ("P5", g)):
            if v: cov[k] += 1
        if a or b or d_ or f or g: cov["union"] += 1
        else: rem += 1
    print(f"n=5, card 4, primitive subsets of [1,{hi}]: {tot} sets")
    for k in ("P1'", "P2", "P3", "P4", "P5"):
        print(f"    {k:>4} : {cov[k]:>8}  ({100*cov[k]/tot:5.2f}%)")
    print(f"    UNION: {cov['union']:>8}  ({100*cov['union']/tot:5.2f}%)")
    print(f"    residue left: {rem:>8}  ({100*rem/tot:5.2f}%)")
    print()
