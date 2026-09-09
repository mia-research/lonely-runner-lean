r"""
ok_reflect_leaf_v1 -- Theorem R applied to the DROPPED-UNIT leaf.

Claim A.  uncovered(1-x) = { 7-r : r in uncovered(x) }.  So S = { x : uncovered nonempty }
          satisfies  S = 1 - S  for EVERY leaf and every speed set.  Safe-measure work
          therefore only ever needs [0,1/2).
Claim B.  The load-bearing window W2 = [3/7,4/7) of the extremal (3,4) case is FORCED by
          this: x = 1/2 is the fixed point of x -> 1-x, and 7-2 = 5, so a residue uncovered
          on one side must be replaced by its reflection partner on the other.  The
          "single-residue trap" is not an accident of that case; it is where the symmetry
          acts.  And the absent pair {3,4} is itself one of the four reflection pairs.
"""
from fractions import Fraction as F

def bad(e, t):
    return frozenset(r for r in range(8) if (e*r + t) % 8 in (0, 7))
def cells(S):
    pts = {F(0), F(1)}
    for e in S:
        for j in range(1, e+1):
            q = F(j, e)
            if 0 < q < 1: pts.add(q)
    p = sorted(pts); return list(zip(p, p[1:]))
def fl(e, a):
    v = e*a; return v.numerator // v.denominator
def uncovered(S, x):
    c = set()
    for e in S: c |= bad(e, fl(e, x))
    return frozenset(r for r in range(8) if r not in c)

EXTREMAL = [1,2,5,6,7]          # absent pair (3,4); |S| = 19/35
print("Extremal dropped-unit case: E_non =", EXTREMAL, " absent pair (3,4)")

mis = 0; n = 0; Smeas = F(0)
for a, b in cells(EXTREMAL):
    x = a + (b-a)/2
    lhs = uncovered(EXTREMAL, 1-x)
    rhs = frozenset((7-r) % 8 for r in uncovered(EXTREMAL, x))
    n += 1
    if lhs != rhs: mis += 1
    if uncovered(EXTREMAL, a): Smeas += b - a      # entry evaluation for the measure
print(f"  Claim A: uncovered(1-x) == 7-uncovered(x) : {mis} mismatches over {n} cells")
print(f"  |S| (entry evaluation) = {Smeas} = {float(Smeas):.6f}   (doc says 19/35 = {float(F(19,35)):.6f})")

# S = 1-S as a set
sym = 0
for a, b in cells(EXTREMAL):
    x = a + (b-a)/2
    if bool(uncovered(EXTREMAL, x)) != bool(uncovered(EXTREMAL, 1-x)): sym += 1
print(f"  Claim A': S == 1-S : {sym} mismatches")

print("\n  Claim B: the window W2 = [3/7,4/7), read at entry and exit on each side of 1/2")
for lo, hi in [(F(3,7), F(1,2)), (F(1,2), F(4,7))]:
    ent = uncovered(EXTREMAL, lo)
    ex  = uncovered(EXTREMAL, lo + (hi-lo)*F(999999,1000000))
    print(f"    [{lo}, {hi}) : entry uncovered = {sorted(ent)}   exit uncovered = {sorted(ex)}"
          f"   {'CONSTANT' if ent==ex else 'VARIES'}")
print(f"    reflection partner of 2 is {7-2}; fixed point of x -> 1-x is 1/2. "
      f"Both windows meet at exactly 1/2.")

print("\n  All 18 absent-pairs: which are self-paired under r -> 7-r?")
pairs = [(a,b) for a in range(8) for b in range(a+1,8)]
selfp = [(a,b) for a,b in pairs if {(7-a)%8,(7-b)%8} == {a,b}]
print(f"    self-paired absent-pairs: {selfp}")
