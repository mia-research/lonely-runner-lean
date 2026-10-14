"""Does `Flanks.lonely_of_flank_unkillable` match what the batch machine computes?

The machine's anchor (batch_machine_v1.py docstring): cover {(2,1),(8,1),(8,3),(8,5),(8,7)} reproduces
EIGHTH_FAMILY_v1 -- U = empty at e in {1/8, 3/8}; K = {1/4} at e = 1/2; K = {3/4} at e = 5/8;
K = EMPTY at e = 7/8.  The K = empty flank is the case the new theorem covers.

Scale-normalised to d_max = 8 the family is {1, 3, 4, 5, 7, x, 8} and that flank is the difference 7.
This checks, in exact arithmetic, that the theorem's hypotheses hold there with the machine's own P and U:

  hlat : every fixed d has Int.fract (P * (d/e)) = 0
  hU   : every fixed d is clear at every opening r in U
  hkill: every ON-LATTICE x fails to shadow the whole class of some r in U

and that the theorem's OFF-lattice case needs no hypothesis (class_killer_int rules it out).
"""
from fractions import Fraction as F

n = 8; INV = F(1, n)
def fract(z): return z - (z.numerator // z.denominator)
def cd(z):    return min(fract(z), 1 - fract(z))
def opening(e, k): return (F(k) + INV) / e
def clear(d, e, k): return cd(d * opening(e, k)) >= INV

FIXED = [F(1), F(3), F(4), F(5), F(7), F(8)]
E = F(7)
P = 7
U = [1, 3]

print(f"eighth family, flank e = {E}, machine's P = {P}, U = {U}\n")

print("  hlat : Int.fract(P*(d/e)) = 0 for every fixed d")
ok = all(fract(F(P) * (d / E)) == 0 for d in FIXED)
for d in FIXED:
    print(f"     d = {d}:  P*(d/e) = {F(P)*(d/E)}   fract = {fract(F(P)*(d/E))}")
print(f"     all on the lattice: {ok}\n")

print("  U is the uncovered residue set: no fixed d blocks r, for r in U")
hU = True
for r in U:
    per = [(str(d), clear(d, E, r)) for d in FIXED]
    good = all(c for _, c in per)
    hU &= good
    print(f"     r = {r}: every fixed d clear = {good}   {per}")
print(f"     hU holds: {hU}")
blocked_elsewhere = [r for r in range(P) if r not in U and all(clear(d, E, r) for d in FIXED)]
print(f"     residues outside U that are also uncovered (should be none): {blocked_elsewhere}\n")

print(f"  hkill : every ON-LATTICE x fails on some r in U")
print(f"     on-lattice means Int.fract({P}*(x/{E})) = 0, i.e. x an integer here")
hkill = True
for x in range(1, 8):
    xs = F(x)
    assert fract(F(P) * (xs / E)) == 0, "not on the lattice"
    found = None
    for r in U:
        for j in range(3):
            if clear(xs, E, r + j * P): found = (r, j); break
        if found: break
    hkill &= found is not None
    print(f"     x = {x}: clear at (r, j) = {found}"
          f"   -> opening k = {found[0] + found[1]*P if found else None}")
print(f"     hkill holds for every integer x in 1..7: {hkill}\n")

print("  OFF-lattice x needs no hypothesis (class_killer_int). Spot check, 1000 non-integers:")
import random
random.seed(1); bad = 0
for _ in range(1000):
    xs = F(random.randint(1, 5000), random.randint(2, 97))
    if xs <= 0 or xs >= 8 or fract(F(P) * (xs / E)) == 0: continue
    hit = any(clear(xs, E, U[0] + j * P) or clear(xs, E, U[1] + j * P) for j in range(200))
    if not hit: bad += 1
print(f"     off-lattice values with no clear opening in the classes of U: {bad} (expected 0)")
print(f"\n  VERDICT: theorem hypotheses match the machine at its anchor: "
      f"{ok and hU and hkill and bad == 0 and not blocked_elsewhere}")
