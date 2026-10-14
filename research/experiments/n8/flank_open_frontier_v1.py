"""How wide is the flank route's open case at order 8?

`Flanks.lonely_iff_exists_flank` is an iff: the subject is lonely somewhere iff some flank has a lonely
opening. `position_at_flank` + `fractional_ratio_circDist`: at flank `e`'s k-th opening the runner at `d`
sits at circDist(k*f + rho/n) with rho = d/e and f = frac(rho). So

  * the flank itself sits at exactly 1/n -- CLEAR, by the open-zone convention;
  * an INTEGER ratio A is clear at every opening iff n does not divide A (integer_ratio_clear_iff)
    -- it never moves, so it is settled once;
  * only the NON-INTEGER ratios move with k.

So Existence at a flank has j = #(non-integer ratios) moving parts, j <= n-2 = 6. Proved coverage:
j = 1 by lonely_opening_of_one_fractional; j = 2,3 by Propositions 6.10-6.11. Section 6.9 states the
open case as four or more non-integer ratios. And only ONE of the 7 flanks needs to work.

This measures, per arrangement, min over flanks of j, restricted to flanks that are not immediately
dead -- i.e. how often EVERY flank has j >= 4, which is where the open case actually bites.
"""
import sys, random
from fractions import Fraction as F
from collections import Counter

n = 8; INV = F(1, n)
def fract(x): return x - (x.numerator // x.denominator)
def cd(x):    return min(fract(x), 1 - fract(x))

def flank_profile(ds, e):
    """(j, dead) for flank e: j = number of non-integer ratios among the other differences;
    dead = some integer ratio divisible by n (that runner is in the way at EVERY opening)."""
    j = 0; dead = False
    for d in ds:
        if d == e: continue
        rho = F(d, 1) / e if not isinstance(d, F) else d / e
        if rho.denominator == 1:
            if rho.numerator % n == 0: dead = True
        else:
            j += 1
    return j, dead

def lonely_at_some_opening(ds, e, kmax=4000):
    for k in range(kmax):
        t = (F(k) + INV) / e
        if all(cd(d * t) >= INV for d in ds): return k
    return None

NS = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
VMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 60
random.seed(20260917)

print(f"order {n}: the flank route's open frontier (j = non-integer ratios at a flank)")
print(f"proved: j <= 3 (one-fractional lemma; Props 6.10-6.11).  OPEN: j >= 4  (section 6.9)")
print(f"{NS} shuffled arrangements, integer differences <= {VMAX}\n")

minj = Counter(); allopen = 0; solved_by = Counter(); nolonely = 0
for _ in range(NS):
    dsi = sorted(random.sample(range(1, VMAX + 1), 7))
    ds = [F(d) for d in dsi]
    profs = []
    for e in ds:
        j, dead = flank_profile(ds, e)
        if not dead: profs.append((j, e))
    if not profs:
        minj[None] += 1; continue
    m = min(j for j, _ in profs)
    minj[m] += 1
    if m >= 4: allopen += 1
print(f"  distribution of  min over live flanks of j :")
for k in sorted(x for x in minj if x is not None):
    print(f"     j = {k}: {minj[k]:7}  ({100*minj[k]/NS:5.2f}%)")
if None in minj: print(f"     every flank dead: {minj[None]}")
print(f"\n  arrangements where EVERY live flank has j >= 4 (the open case, unavoidable): "
      f"{allopen}  ({100*allopen/NS:.2f}%)")
print(f"  arrangements with some flank at j <= 3 (covered in principle): "
      f"{NS-allopen-minj.get(None,0)}  ({100*(NS-allopen-minj.get(None,0))/NS:.2f}%)")

# do the j>=4-only arrangements still have a lonely flank opening?
print(f"\n  for a sample of the open-case arrangements, is there a lonely flank opening anyway?")
random.seed(5); checked = 0; found = 0; ks = []
while checked < 40:
    dsi = sorted(random.sample(range(1, VMAX + 1), 7)); ds = [F(d) for d in dsi]
    profs = [(flank_profile(ds, e), e) for e in ds]
    live = [(j, e) for (j, dead), e in profs if not dead]
    if not live or min(j for j, _ in live) < 4: continue
    checked += 1
    hit = None
    for j, e in live:
        k = lonely_at_some_opening(ds, e)
        if k is not None: hit = (e, k); break
    if hit: found += 1; ks.append(hit[1])
print(f"     {found}/{checked} have one;  opening index k needed: "
      f"min {min(ks) if ks else '-'}, median {sorted(ks)[len(ks)//2] if ks else '-'}, max {max(ks) if ks else '-'}")
