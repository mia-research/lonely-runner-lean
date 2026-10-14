"""Where does the flank route run out?

Flanks.lonely_iff_exists_flank is an IFF, so Existence at 8 is EXACTLY:

  for every 7 positive reals ds, there are e in ds and k in N with
      circDist(k*f_j + rho_j/n) >= 1/n   for every other d_j,
  where rho_j = d_j/e and f_j = fract(rho_j).   (Flanks.fractional_ratio_circDist)

So each other runner is a rotation by f_j with a STARTING OFFSET rho_j/n that is not free:
it is determined by the same ratio.  This script measures where the route becomes hard.
"""
import random, math
from itertools import combinations

n = 8
THRESH = 1.0 / n

def circ(x):
    f = x - math.floor(x)
    return min(f, 1 - f)

def flank_clear_k(ds, e, K):
    """Smallest k <= K at which flank e's opening is lonely; None if none found."""
    others = [d for d in ds if d != e]
    rhos = [d / e for d in others]
    for k in range(K + 1):
        if all(circ(k * (r - math.floor(r)) + r / n) >= THRESH for r in rhos):
            return k
    return None

def dead(ds, e):
    """e is a DEAD flank: some other ratio is a multiple of n (that runner never leaves)."""
    for d in ds:
        if d == e:
            continue
        r = d / e
        if r >= n and abs(r / n - round(r / n)) < 1e-12:
            return True
    return False

random.seed(20260917)
K = 400
best_ks, worst = [], []
dmax_is_best = 0
nfree = {}
for _ in range(3000):
    ds = sorted(random.uniform(1, 50) for _ in range(7))
    ks = {}
    for e in ds:
        kk = flank_clear_k(ds, e, K)
        if kk is not None:
            ks[e] = kk
    nfree[len(ks)] = nfree.get(len(ks), 0) + 1
    if not ks:
        worst.append((None, ds))
        continue
    bk = min(ks.values())
    best_ks.append(bk)
    if ks.get(ds[-1]) == bk:
        dmax_is_best += 1
    if bk >= 8:
        worst.append((bk, ds))

best_ks.sort()
print(f"arrangements                      : 3000   (7 real differences, uniform in [1,50])")
print(f"searched openings per flank       : k = 0 .. {K}")
print(f"arrangements with NO lonely opening on ANY flank within K : "
      f"{sum(1 for w in worst if w[0] is None)}")
print()
print("smallest k over the best flank:")
print(f"  min {best_ks[0]}   median {best_ks[len(best_ks)//2]}   "
      f"90th {best_ks[int(.9*len(best_ks))]}   99th {best_ks[int(.99*len(best_ks))]}   max {best_ks[-1]}")
print(f"  k = 0 works for            : {sum(1 for b in best_ks if b == 0)} / {len(best_ks)}")
print(f"  k <= 2 works for           : {sum(1 for b in best_ks if b <= 2)} / {len(best_ks)}")
print()
print(f"flanks with SOME lonely opening (of 7), distribution: {dict(sorted(nfree.items()))}")
print(f"the largest difference is a best flank in            : {dmax_is_best} / {len(best_ks)}")

# ---------------------------------------------------------------------------
# Random reals are the EASY case.  Shadowing needs rational ratios with small
# denominators, so search integer arrangements exhaustively instead.
print()
print("=" * 72)
print("INTEGER arrangements: every 7-subset of [1,20]")
from fractions import Fraction

def circ_q(x: Fraction) -> Fraction:
    f = x - (x.numerator // x.denominator)
    return min(f, 1 - f)

def flank_free_exact(ds, e, K):
    """Exact: smallest k <= K with flank e lonely. Ratios are rational, so the
    verdict is periodic in k with period = lcm of the ratio denominators; K is set
    above that period so 'None' means genuinely shadowed, not merely unsearched."""
    others = [d for d in ds if d != e]
    rs = [Fraction(d, e) for d in others]
    per = 1
    for r in rs:
        f = r - (r.numerator // r.denominator)
        per = per * f.denominator // math.gcd(per, f.denominator)
    for k in range(min(K, per)):
        if all(circ_q(k * (r - (r.numerator // r.denominator)) + r / n) >= Fraction(1, n)
               for r in rs):
            return k, per
    return None, per

tot = 0
freedist = {}
hard = []
for S in combinations(range(1, 21), 7):
    tot += 1
    free = []
    for e in S:
        k, per = flank_free_exact(S, e, 100000)
        if k is not None:
            free.append((e, k))
    freedist[len(free)] = freedist.get(len(free), 0) + 1
    if len(free) <= 1:
        hard.append((S, free))

print(f"  7-subsets of [1,20]              : {tot}")
print(f"  free flanks per arrangement      : {dict(sorted(freedist.items()))}")
print(f"  arrangements with 0 free flanks  : {freedist.get(0,0)}")
print(f"  arrangements with 1 free flank   : {freedist.get(1,0)}")
if hard:
    print(f"\n  the tightest arrangements (<=1 free flank), first 12:")
    for S, free in hard[:12]:
        print(f"    {S}   free: {free}")
