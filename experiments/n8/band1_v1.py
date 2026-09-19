"""R < 16 says [1,7] u [9,15] has a clear point.  For INTEGER readings block_periodic makes band 1
an exact +8 shift of band 0, so it adds nothing.  For NON-INTEGER readings periodicity fails.

Does band 1 ever do work?  Measure: band 0 empty but band 1 non-empty.
"""
from fractions import Fraction as F
import random

def clear(S, x):
    for s in S:
        y = s*x
        k = round(y/8)
        if abs(y - 8*k) < 1: return False
    return True

def band_nonempty(S, lo, hi, step=F(1,240)):
    """Exact scan on a fine rational grid; endpoints of bad intervals have denominators dividing
    the numerators of the readings, so a fine grid detects non-empty reliably for a check."""
    x = lo
    while x <= hi:
        if clear(S, x): return True, x
        x += step
    return False, None

rng = random.Random(20260919)
print(f"{'arm':<34} {'profiles':>9} {'band0 empty':>12} {'band1 saves':>12}")
for label, gen in (
    ("integer readings", lambda: [F(1)] + sorted(F(rng.randint(2,60)) for _ in range(6))),
    ("rational, denominators <= 4", lambda: [F(1)] + sorted(F(rng.randint(2,200), rng.randint(1,4)) for _ in range(6))),
    ("rational, denominators <= 12", lambda: [F(1)] + sorted(F(rng.randint(2,400), rng.randint(1,12)) for _ in range(6))),
):
    tot=b0e=saves=0
    for _ in range(1200):
        S = gen()
        if len(set(S)) != 7 or min(S) != 1: continue
        tot += 1
        ok0,_ = band_nonempty(S, F(1), F(7))
        if ok0: continue
        b0e += 1
        ok1,_ = band_nonempty(S, F(9), F(15))
        if ok1: saves += 1
    print(f"  {label:<32} {tot:>9,} {b0e:>12,} {saves:>12,}")
print()
print("  'band1 saves' = band 0 has no clear point but band 1 does -- the only case where")
print("  R < 16 is strictly weaker than R <= 7, i.e. where the second band does real work.")
