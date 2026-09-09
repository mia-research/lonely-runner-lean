r"""
ok_reflect_general_v1 -- how far does Theorem R go?

The proof of  bad(e, e-1-t) = { 7-r : r in bad(e,t) }  ran
      e(7-r) + (e-1-t)  =  8e - 1 - (er + t)  =  -1 - (er+t)   (mod 8)
and NEVER used e odd.  So it should hold for EVERY integer e, divisible speeds included.
If so, the whole n=8 bridge carries an exact Z/2 symmetry:

      x -> 1-x   acts on the blocked-residue set by   r -> 7-r.

Tests:
 (1) the algebraic identity for all e mod 8 (0..7) and all t mod 8;
 (2) the GLOBAL equivariance  cover(1-x) = 7 - cover(x)  on random mixed speed sets
     (units AND divisible speeds together), exact rationals, entry evaluation;
 (3) consequence: U = {all 8 blocked} satisfies U = 1-U, and for any target set T the
     set {x : T blocked} reflects to {x : 7-T blocked}.  So a leaf whose target T
     satisfies 7-T = T has a REFLECTION-SYMMETRIC S.
"""
from fractions import Fraction as F
from math import gcd
import random, itertools

def bad(e, t):
    return frozenset(r for r in range(8) if (e*r + t) % 8 in (0, 7))

print("(1) identity  bad(e, e-1-t) == { 7-r : r in bad(e,t) }  for ALL e,t mod 8:")
fails = [(e,t) for e in range(8) for t in range(8)
         if bad(e, (e-1-t) % 8) != frozenset((7-r) % 8 for r in bad(e, t))]
print(f"    failures over all 64 (e mod 8, t mod 8) pairs: {len(fails)}  {fails[:5]}")

# also check with real (non-reduced) e, since t_e = floor(e x) is not reduced mod 8
fails2 = [(e,t) for e in range(1, 60) for t in range(-20, 60)
          if bad(e, e-1-t) != frozenset((7-r) % 8 for r in bad(e, t))]
print(f"    failures over e = 1..59, t = -20..59: {len(fails2)}")

def cells(S):
    pts = {F(0), F(1)}
    for e in S:
        for j in range(1, e+1):
            q = F(j, e)
            if 0 < q < 1: pts.add(q)
    p = sorted(pts); return list(zip(p, p[1:]))
def fl(e, a):
    v = e*a; return v.numerator // v.denominator
def cover(S, x):
    c = set()
    for e in S: c |= bad(e, fl(e, x))
    return frozenset(c)

print("\n(2) global equivariance  cover(1-x) == 7 - cover(x)  on MIXED speed sets:")
random.seed(7)
tot = mism = 0
sets_tested = []
for trial in range(12):
    k = random.choice([5, 6, 7])
    S = random.sample(range(1, 40), k)
    sets_tested.append(tuple(sorted(S)))
    for a, b in cells(S):
        x = a + (b - a)/2          # interior point, avoids breakpoints on both sides
        lhs = cover(S, 1 - x); rhs = frozenset((7-r) % 8 for r in cover(S, x))
        tot += 1
        if lhs != rhs: mism += 1
print(f"    {len(sets_tested)} random speed sets (units and divisible mixed), "
      f"{tot} interior points, mismatches: {mism}")
print(f"    example sets: {sets_tested[:3]}")

print("\n(3) consequence check: is U = 1-U on those sets?")
bad_u = 0; tot_u = 0
for S in sets_tested:
    for a, b in cells(list(S)):
        x = a + (b - a)/2
        tot_u += 1
        if (len(cover(list(S), x)) == 8) != (len(cover(list(S), 1-x)) == 8): bad_u += 1
print(f"    U vs 1-U mismatches over {tot_u} points: {bad_u}")
print("\n    T with 7-T = T (so {x : T blocked} is reflection-symmetric):")
symT = [T for k in range(1,9) for T in itertools.combinations(range(8), k)
        if frozenset((7-r)%8 for r in T) == frozenset(T)]
print(f"    {len(symT)} of 255 non-empty targets are self-paired; the 4 pairs are "
      f"{{0,7}},{{1,6}},{{2,5}},{{3,4}}")
