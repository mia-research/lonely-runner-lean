"""At a flank, what actually blocks -- the number of non-integer ratios, or a slot-sharer?

`integer_ratio_clear_iff` (Flanks.lean:66): a runner at INTEGER ratio A to the flank is clear at EVERY
opening iff n does not divide A. So integer ratios are resolved once and for all:
   n does not divide A -> clear forever;  n divides A -> in the way forever (a slot-sharer, flank dead).
`exists_clear_step`: a single NON-integer ratio cannot stay in the way -- it always has a clear opening.

So movers escape and integers are settled. The claim "j >= 4 non-integer ratios is the open case" (section
6.9) describes where Props 6.10-6.11 apply, NOT where the difficulty is. This tests which one predicts a
flank failing.

For each flank: dead (a slot-sharer) / live; j = non-integer ratios; does a lonely opening exist within
KMAX. Reports whether any LIVE flank fails, and whether j predicts failure.
"""
import sys, random
from fractions import Fraction as F
from collections import Counter

n = 8; INV = F(1, n)
def fract(x): return x - (x.numerator // x.denominator)
def cd(x):    return min(fract(x), 1 - fract(x))

def profile(ds, e, KMAX):
    j = 0; dead = False
    for d in ds:
        if d == e: continue
        rho = d / e
        if rho.denominator == 1:
            if rho.numerator % n == 0: dead = True
        else: j += 1
    hit = None
    for k in range(KMAX):
        t = (F(k) + INV) / e
        if all(cd(d * t) >= INV for d in ds): hit = k; break
    return dead, j, hit

NS   = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
VMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 60
KMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
random.seed(20260917)

print(f"order {n}: what blocks a flank?  {NS} arrangements, differences <= {VMAX}, openings k < {KMAX}\n")
live_ok = live_fail = dead_ok = dead_fail = 0
byj_ok = Counter(); byj_fail = Counter(); fails = []
arr_no_flank = 0
for _ in range(NS):
    dsi = sorted(random.sample(range(1, VMAX + 1), 7))
    ds = [F(d) for d in dsi]
    any_hit = False
    for e in ds:
        dead, j, hit = profile(ds, e, KMAX)
        if hit is not None: any_hit = True
        if dead:
            dead_ok += (hit is not None); dead_fail += (hit is None)
        else:
            if hit is not None: live_ok += 1; byj_ok[j] += 1
            else:
                live_fail += 1; byj_fail[j] += 1
                if len(fails) < 5: fails.append((dsi, str(e), j))
    if not any_hit: arr_no_flank += 1

print(f"  LIVE flanks (no slot-sharer):")
print(f"     with a lonely opening : {live_ok}")
print(f"     WITHOUT one          : {live_fail}")
print(f"  DEAD flanks (a slot-sharer, in the way at every opening):")
print(f"     with a lonely opening : {dead_ok}   (must be 0 -- the sharer never clears)")
print(f"     without one           : {dead_fail}")
print(f"\n  arrangements with NO flank having a lonely opening: {arr_no_flank}/{NS}")
print(f"\n  live flanks WITH a lonely opening, by j: {dict(sorted(byj_ok.items()))}")
print(f"  live flanks WITHOUT one,          by j: {dict(sorted(byj_fail.items())) or 'none'}")
for f in fails: print(f"     failing live flank: differences {f[0]}, flank {f[1]}, j = {f[2]}")
print()
if live_fail == 0:
    print(f"  => j does NOT predict failure: every live flank had a lonely opening.")
    print(f"     The blocking object is the SLOT-SHARER (integer ratio divisible by {n}), which is")
    print(f"     decided by an integer test, not the count of non-integer ratios.")
else:
    print(f"  => some live flanks fail; j = {sorted(byj_fail)} among them.")
