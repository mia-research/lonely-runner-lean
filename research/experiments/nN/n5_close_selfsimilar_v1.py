"""Closing the self-similar family.

Reduced band problem B(ms, e):  exists r in [0,e) with  m_i * r mod e  in [e/5, 4e/5] for all i.

Two reductions:
 (R1) SCALING.  If gcd(l, e) = 1 then r -> l*r is a bijection of Z/e, so B((l*m_i), e) = B(ms, e).
      So only PRIMITIVE triples matter -- and the difference set being primitive forces
      gcd(5l, e) = 1, hence gcd(l, e) = 1.  The reduction always applies.
 (R2) WINDOW.  S = sup_t min ||m_i t|| exceeds 1/5, so the lonely set contains an interval of
      width 2(S - 1/5)/m3; it contains a point r/e once e > m3/(2(S-1/5)).

So each primitive triple is closed above an explicit bound, and below it is a FINITE check.
"""
import math
from itertools import combinations
from fractions import Fraction as F

def norm(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)

def sup_min(ms):
    dens = {2*m for m in ms}
    for a, b in combinations(ms, 2):
        dens.add(a+b)
        if a != b: dens.add(abs(a-b))
    best = F(0)
    for q in dens:
        for k in range(0, q//2 + 2):
            t = F(k, q)
            if t > F(1,2): continue
            v = min(norm(F(m) * t) for m in ms)
            if v > best: best = v
    return best

def band_ok(ms, e):
    return any(all(e <= 5*((m*r) % e) <= 4*e for m in ms) for r in range(e))

HARD = [(1,2,3), (1,2,6), (1,3,4), (1,5,6), (2,3,5)]
print("=== (R1) scaling reduction, verified ===")
bad = 0; tot = 0
for ms in HARD:
    for l in (2,3,4,6,7,11):
        for e in range(6, 90):
            if math.gcd(l, e) != 1: continue
            tot += 1
            if band_ok(tuple(l*m for m in ms), e) != band_ok(ms, e): bad += 1
print(f"   checked {tot} (triple, scale, modulus) combinations:  mismatches = {bad}")
print()
print("=== (R2) the window bound, and the finite range left below it ===")
print(f"{'triple':>12} {'S':>6} {'window closes e >':>18} {'finite range':>16} {'failures there':>15}")
for ms in HARD:
    S = sup_min(ms)
    bound = F(ms[-1]) / (2*(S - F(1,5)))
    lo = 5*ms[-1]                      # free bound from the difference set
    hi = math.floor(bound)
    rng = [e for e in range(lo+1, hi+1) if math.gcd(5, e) == 1]
    fails = [e for e in rng if not band_ok(ms, e)]
    print(f"{str(ms):>12} {str(S):>6} {float(bound):>18.2f} {f'{lo+1}..{hi}':>16} {str(fails):>15}")
print()
print("=== and above the bound, spot-check that the window really does deliver ===")
for ms in HARD:
    S = sup_min(ms); bound = F(ms[-1]) / (2*(S - F(1,5)))
    hi = math.floor(bound)
    bad2 = [e for e in range(hi+1, hi+60) if math.gcd(5,e)==1 and not band_ok(ms, e)]
    print(f"   {str(ms):>12}: e in ({hi}, {hi+60}) coprime to 5 -- failures: {bad2}")
