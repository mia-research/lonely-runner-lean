"""Independent check of every family the batch emits: is the theorem actually true?

For each emitted family, sample x across rationals and integers in (0, M) and confirm the subject has a
lonely opening AT THE CLAIMED FLANK. This does not read the Lean; it re-derives the claim from the
definitions, so agreement is a check and not a restatement.
"""
import sys, random
from fractions import Fraction as F
sys.path.insert(0, 'experiments/n8')
from gen_census_batch_v1 import instances, clear, INV, cd
from fractions import Fraction as F

n = 8
def lonely(ds, e, k):
    t = (F(k) + INV) / e
    return all(cd(F(d) * t) >= INV for d in ds)

inst = instances()
random.seed(20260917)
print(f"verifying {len(inst)} emitted families\n")
bad = 0; tot = 0
for i, ((diffs, e, P, U), ncov) in enumerate(inst, 1):
    M = max(diffs); fixed = list(diffs)
    fails = []
    xs = [F(v) for v in range(1, M)]
    xs += [F(random.randint(1, 20*M), random.randint(1, 40)) for _ in range(300)]
    for x in xs:
        if not (0 < x < M): continue
        ds = fixed + [x]
        tot += 1
        # exists_clear_step's index scales like 1/min(f, 1-f) for f the step's fractional part,
        # so the search bound must be adaptive -- a fixed window under-searches and reports false
        # failures (it did, on first run: 26 of 62, all spurious).
        fr = F(P) * (x / e); fr = fr - (fr.numerator // fr.denominator)
        step = min(fr, 1 - fr) if fr != 0 else F(1)
        lim = (int(1 / step) + 20) * P + 40 if step != 0 else 4 * P + 8
        if not any(lonely(ds, e, k) for k in range(0, lim)):
            fails.append(str(x))
    if fails:
        bad += 1
        print(f"  family {i:2} diffs={fixed} e={e}: FAILURES {fails[:4]}")
print(f"  x values tested: {tot}")
print(f"  families with any failure: {bad}/{len(inst)}")
print(f"\n  {'ALL FAMILIES VERIFIED' if bad == 0 else 'VERIFICATION FAILED'}")
