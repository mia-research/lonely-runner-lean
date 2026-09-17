"""Where the flank route is actually tight, and whether it ever fails.

The mirror of Theorem 4.8 decides flank d_max at its first opening whenever every other
difference lies in [d_max/9, 7*d_max/9].  So the cases it does NOT decide are those with a
difference below d_max/9 (large spread) or just under d_max.  This searches there.

Ratios are rational, so the verdict at flank e is PERIODIC in k with period = lcm of the
fractional-part denominators.  Searching one full period therefore DECIDES shadowing
exactly -- 'no free opening' here is a proof for that arrangement, not a failed search.
"""
import math, random
from fractions import Fraction
from itertools import combinations

n = 8
TH = Fraction(1, n)

def circ_q(x: Fraction) -> Fraction:
    f = x - (x.numerator // x.denominator)
    return min(f, 1 - f)

def free_k(ds, e, cap=2000000):
    others = [d for d in ds if d != e]
    rs = [Fraction(d, e) for d in others]
    fr = [r - (r.numerator // r.denominator) for r in rs]
    per = 1
    for f in fr:
        per = per * f.denominator // math.gcd(per, f.denominator)
    if per > cap:
        return None, per, False                      # not decided
    for k in range(per):
        if all(circ_q(k * f + r / n) >= TH for f, r in zip(fr, rs)):
            return k, per, True
    return None, per, True                           # DECIDED shadowed

def analyse(ds):
    free, decided = [], True
    for e in ds:
        k, per, ok = free_k(ds, e)
        if not ok:
            decided = False
        elif k is not None:
            free.append((e, k))
    return free, decided

def mirror48(ds):
    dm = max(ds)
    return all(Fraction(dm, 9) <= Fraction(d) <= Fraction(7 * dm, 9) for d in ds if d != dm)

random.seed(20260917)
print("Targeted search: integer arrangements the mirror of 4.8 does NOT decide")
print("(some difference below d_max/9, or in (7*d_max/9, d_max))")
print()
tested = nomirror = zero_free = 0
tight = []
maxk = 0
for _ in range(60000):
    hi = random.choice([30, 60, 120, 400, 1000])
    ds = tuple(sorted(random.sample(range(1, hi + 1), 7)))
    if mirror48(ds):
        continue
    nomirror += 1
    free, decided = analyse(ds)
    if not decided:
        continue
    tested += 1
    if not free:
        zero_free += 1
        tight.append((0, ds, free))
    elif len(free) <= 2:
        tight.append((len(free), ds, free))
    if free:
        maxk = max(maxk, min(k for _, k in free))

print(f"  sampled arrangements not decided by the mirror : {nomirror}")
print(f"  of those, fully DECIDED by one full period     : {tested}")
print(f"  with ZERO free flanks (would refute Existence) : {zero_free}")
print(f"  largest 'smallest k over the best flank'       : {maxk}")
print()
tight.sort(key=lambda t: t[0])
print(f"  tightest found (<=2 free flanks): {len(tight)}")
for nf, ds, free in tight[:15]:
    print(f"    free={nf:2d}  {ds}   spread={max(ds)/min(ds):.1f}   {free}")
