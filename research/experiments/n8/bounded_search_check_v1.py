"""Is the bounded search genuinely complete for whole-number differences?

Flanks.lonely_iff_bounded_search claims, for ds a set of positive INTEGERS:

    lonely somewhere  <->  lonely at some flank e in ds and some opening k < e

If that is right, searching k < e at each flank must never MISS a set that a much wider
search finds. That is the direction worth testing: a false 'no' would be the damaging error.
"""
import random
from fractions import Fraction as F

def circd(x):
    f = x - (x.numerator // x.denominator)
    return min(f, 1 - f)

def lonely(ds, t):
    return all(circd(d * t) >= F(1, 8) for d in ds)

def bounded(ds):
    for e in ds:
        for k in range(int(e)):
            if lonely(ds, (F(k) + F(1, 8)) / e):
                return (e, k)
    return None

def wide(ds, KMAX=4000):
    for e in ds:
        for k in range(KMAX):
            if lonely(ds, (F(k) + F(1, 8)) / e):
                return (e, k)
    return None

rng = random.Random(20260917)
agree = miss = tot = 0
for _ in range(4000):
    ds = sorted({F(x) for x in rng.sample(range(1, 200), 7)})
    tot += 1
    b, w = bounded(ds) is not None, wide(ds) is not None
    if b == w: agree += 1
    elif w and not b: miss += 1
print(f"integer difference sets tested            : {tot}")
print(f"bounded (k < e) and wide (k < 4000) agree : {agree}")
print(f"bounded says NO where wide says YES       : {miss}")
print(f"  cost of the bounded search: sum of e over the flanks, median "
      f"{sorted(sum(int(d) for d in sorted({F(x) for x in rng.sample(range(1,200),7)})) for _ in range(200))[100]} openings")
print()
if miss == 0:
    print("  The bounded search never misses. So for whole-number differences the question")
    print("  'is this set lonely somewhere' is DECIDED by a finite check, and running that")
    print("  check on more sets -- which is what the census is -- produces no new mathematics.")
