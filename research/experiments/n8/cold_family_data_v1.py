"""Data for a COLD census family, taken through Flanks.lonely_of_flank_unkillable.

Machine row (results/batch_machine_v1.out):
  cover ((2,1),(5,1),(10,1),(10,3),(10,7)), pinned 1/10, 1/5, 3/10, 1/2, 7/10, s = 5
  flank '1/2': ('U', 3, 'K', [])  -- always free, the Version A route

Scaled by 10 (E = 1 -> d_max = 10) the family is {1, 2, 3, 5, 7, x, 10}, 0 < x < 10,
and that flank is the difference 5.  Unlike the eighth family this one has no clearance
lemmas in the Lean tree: everything below has to be produced.
"""
from fractions import Fraction as F

n = 8; INV = F(1, n)
def fract(z): return z - (z.numerator // z.denominator)
def cd(z):    return min(fract(z), 1 - fract(z))
def opening(e, k): return (F(k) + INV) / e
def clear(d, e, k): return cd(d * opening(e, k)) >= INV

FIXED = [F(1), F(2), F(3), F(5), F(7), F(10)]
E = F(5)

# period: lcm of denominators of the fractional parts of d/E
from math import lcm
P = 1
for d in FIXED:
    f = fract(d / E)
    if f != 0: P = lcm(P, f.denominator)
print(f"family {{1,2,3,5,7,x,10}}, flank e = {E}")
print(f"  ratios d/e: {[str(d/E) for d in FIXED]}")
print(f"  period P = {P}\n")

U = [r for r in range(P) if all(clear(d, E, r) for d in FIXED)]
print(f"  U (residues mod {P} where every fixed difference is clear) = {U}   |U| = {len(U)}")
print(f"  machine reported |U| = 3 at this flank: {len(U) == 3}\n")

print(f"  hU detail -- phase of each fixed d at each r in U, as p/{8*E} plus an integer:")
for r in U:
    row = []
    for d in FIXED:
        v = d * opening(E, r)          # = d*(r + 1/8)/5
        num = v * 8 * E                # numerator over 8e = 40
        row.append(f"{d}:{num}/{8*E}")
    print(f"     r = {r}: {row}")

print(f"\n  hkill -- on-lattice x means Int.fract(x) = 0, i.e. x in 1..9. Each must fail on some r in U:")
allok = True
for x in range(1, 10):
    xs = F(x); found = None
    for r in U:
        for j in range(4):
            if clear(xs, E, r + j*P): found = (r, j, r + j*P); break
        if found: break
    allok &= found is not None
    v = xs * opening(E, found[2])
    print(f"     x = {x}: clear at r = {found[0]}, j = {found[1]}, opening k = {found[2]}"
          f"   phase = {v*8*E}/{8*E}")
print(f"  every integer x in 1..9 fails on some r in U: {allok}")
print(f"  machine reported K = [] (no killer at all): {allok}")
