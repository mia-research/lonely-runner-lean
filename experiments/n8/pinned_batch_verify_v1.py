"""Independent check of every emitted fully-pinned family.

The witnesses (e, k) were found by the residue-band arithmetic. This re-checks them by the DEFINITION
-- circDist of the exact rational phase -- so it tests the band/circDist equivalence that
Flanks.clear_of_residue_band asserts, not just the arithmetic that produced the witness.
"""
import sys
from fractions import Fraction as F
sys.path.insert(0, 'experiments/n8')
from gen_pinned_batch_v1 import sets_and_witness, band_ok

n = 8; INV = F(1, n)
def fract(z): return z - (z.numerator // z.denominator)
def cd(z):    return min(fract(z), 1 - fract(z))

data = sets_and_witness()
print(f"families: {len(data)}")
bad_def = 0; bad_equiv = 0; checks = 0
for d, e, k, ncov in data:
    t = (F(k) + INV) / e
    for m in d:
        checks += 1
        by_def  = cd(F(m) * t) >= INV
        by_band = band_ok(m, e, k)
        if not by_def:  bad_def += 1
        if by_def != by_band: bad_equiv += 1
print(f"clearance checks: {checks}")
print(f"  failing the DEFINITION (circDist >= 1/8): {bad_def}")
print(f"  where band test and definition DISAGREE: {bad_equiv}")
print()
print(f"  {'ALL VERIFIED' if bad_def == 0 and bad_equiv == 0 else 'VERIFICATION FAILED'}")
