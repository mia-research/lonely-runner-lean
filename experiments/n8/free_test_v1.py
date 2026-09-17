"""The free test and all-or-nothing -- section 0's own per-scale instruments, verified.

OBJECT_REGISTER_v1 section 0:
  The free test : `e` cannot block at gap `D`  <=>  m = 8D/gcd(e, 8D) is even and <= 8
  All-or-nothing: if `D` divides every difference, every candidate at that gap gives the same verdict
  Candidates    : t = a/(8D), a odd mod 8D -- 4D of them at gap D

Theorem 4.10: with integral readings the spine instant indexed by a unit p clears a reading s exactly
when 8 does not divide s, THE SAME FOR EVERY p. That is the scale invariance of the AP: at a scale
dividing every difference there is nothing to search -- one verdict.

This checks both against the definition, so the instrument is the framework's and not my reading of it.
"""
from fractions import Fraction as F
from math import gcd
import random

n = 8; INV = F(1, n)
def fract(z): return z - (z.numerator // z.denominator)
def cd(z):    return min(fract(z), 1 - fract(z))

def blocks_somewhere(e, D):
    """does e fail to be clear at SOME candidate t = a/(8D), a odd mod 8D?"""
    for a in range(1, 8 * D, 2):
        if cd(F(e) * F(a, 8 * D)) < INV: return True
    return False

def free_test(e, D):
    m = 8 * D // gcd(e, 8 * D)
    return (m % 2 == 0) and (m <= 8)

print("free test vs the definition ('e is clear at every candidate of gap D')\n")
ok = 0; tot = 0; mism = []
for e in range(1, 121):
    for D in range(1, 41):
        tot += 1
        a = not blocks_somewhere(e, D)
        b = free_test(e, D)
        if a == b: ok += 1
        elif len(mism) < 6: mism.append((e, D, a, b))
print(f"  agree {ok}/{tot}")
for m in mism: print(f"     e={m[0]} D={m[1]}: definition says free={m[2]}, free test says {m[3]}")

print("\nall-or-nothing: with D dividing every difference, is the verdict the same at every candidate?")
random.seed(3); same = 0; tot2 = 0
for _ in range(400):
    D = random.randint(1, 12)
    ds = sorted({D * random.randint(1, 20) for _ in range(7)})
    if len(ds) < 7: continue
    verdicts = set()
    for a in range(1, 8 * D, 2):
        t = F(a, 8 * D)
        verdicts.add(all(cd(F(d) * t) >= INV for d in ds))
    tot2 += 1; same += (len(verdicts) == 1)
print(f"  identical verdict across all candidates: {same}/{tot2}")

print("\n  and that verdict is 'clear' exactly when no reading d/D is a multiple of 8:")
random.seed(4); ok3 = 0; tot3 = 0
for _ in range(400):
    D = random.randint(1, 12)
    ds = sorted({D * random.randint(1, 20) for _ in range(7)})
    if len(ds) < 7: continue
    clear = all(cd(F(d) * F(1, 8 * D)) >= INV for d in ds)
    nosharer = all((d // D) % 8 != 0 for d in ds)
    tot3 += 1; ok3 += (clear == nosharer)
print(f"  agree {ok3}/{tot3}   (Theorem 4.10)")
