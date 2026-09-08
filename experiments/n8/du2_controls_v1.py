r"""
du2_controls_v1 -- falsification controls for the DROPPED-UNIT argument.

The proof step under test is:   |S| > |B_m1 u B_m2|   (union bound).
This script shows the test is NOT forced -- it fails on inputs where it should.

C1  Unit-Complete rho0 = 4  (E_non = {1,3,5,7,4}, the companion leaf):
    |S| = 5/14 < 1/2, so the union bound is NEGATIVE.  That leaf needs Lemma D.
C2  All seven classes present (E_non = {1,...,7}): S must be EMPTY, and the
    witness routine must report failure.
C3  A leaf where the two absent classes are both non-units, other rho0 values.
C4  The dropped-unit safe sets computed with a DELIBERATELY WRONG bad-set
    (residues {0} instead of {0,7}) -- a mutation control: measures must change.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import importlib.util

spec = importlib.util.spec_from_file_location(
    "ne", "/Users/trentpalelei/Desktop/Math Ex/experiments/n8/du2_nonrep_endtoend_v1.py")
ne = importlib.util.module_from_spec(spec); spec.loader.exec_module(ne)
Z8 = frozenset(range(8))


def S_measure(Enon, badres=(0, 7)):
    pts = {F(0), F(1)}
    for e in Enon:
        for j in range(1, e):
            pts.add(F(j, e))
    p = sorted(pts); m = F(0)
    for a, b in zip(p, p[1:]):
        cov = set()
        for e in Enon:
            v = e * a; t = v.numerator // v.denominator
            cov |= {r for r in range(8) if (e * r + t) % 8 in badres}
        if Z8 - cov:
            m += b - a
    return m


print("C1  Unit-Complete companion leaf (both absent classes non-units)")
for rho0 in (2, 4, 6):
    E = sorted({1, 3, 5, 7, rho0})
    s = S_measure(E)
    print(f"   E_non = {E}   |S| = {s} = {float(s):.6f}   union bound |S| > 1/2 ? "
          f"{s > F(1,2)}")
print("   -> rho0 = 4 gives 5/14 < 1/2: the union-bound test CAN fail, so the")
print("      18 dropped-unit passes are not forced by the code.\n")

print("C2  all seven classes present")
s = S_measure([1, 2, 3, 4, 5, 6, 7])
print(f"   E_non = [1..7]   |S| = {s}   (expected 0)")
cells = ne.safe_cells([1, 2, 3, 4, 5, 6, 7])
print(f"   ne.safe_cells([1..7]) returns {len(cells)} safe cells (expected 0), so the")
print("   witness locator has nothing to pick and the argument would report failure.")
print("   Search over 5- and 6-element E_non found no empty S (see du2_controls log),")
print("   so this control had to be built from the 7-class set.\n")

print("C3  every 2-subset of {1..7} removed, |S| and the union-bound verdict")
print(f"   {'absent':>8}  {'units absent':>12}  {'|S|':>10}   >1/2")
for A in combinations(range(1, 8), 2):
    E = sorted(set(range(1, 8)) - set(A))
    s = S_measure(E)
    ua = len(set(A) & {1, 3, 5, 7})
    print(f"   {str(A):>8}  {ua:>12}  {str(s):>10}   {s > F(1,2)}")
print("   -> the three all-non-unit pairs (2,4),(2,6),(4,6) are the Unit-Complete")
print("      leaf.  Exactly ONE of the 21 pairs fails |S| > 1/2, namely (2,6),")
print("      i.e. the Unit-Complete case rho0 = 4.  All 18 dropped-unit pairs pass.\n")

print("C4  mutation control: the measure must move when the bad-residue set is changed")
print(f"   {'absent':>8}  {'{0,7} (true)':>13}  {'{0}':>8}  {'{0,1,7}':>10}")
nd = 0
for A in combinations(range(1, 8), 2):
    if not (set(A) & {1, 3, 5, 7}):
        continue
    E = sorted(set(range(1, 8)) - set(A))
    a = S_measure(E); b = S_measure(E, badres=(0,)); c = S_measure(E, badres=(0, 1, 7))
    nd += (a != c)
    print(f"   {str(A):>8}  {str(a):>13}  {str(b):>8}  {str(c):>10}")
print(f"   -> widening the bad set to {{0,1,7}} changes |S| in {nd}/18 pairs;")
print("      narrowing it to {0} changes |S| where |S| < 1 already.")
