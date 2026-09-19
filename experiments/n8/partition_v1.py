"""What ARE the correct categories?

By the classical reduction every LRC instance at n=8 is an INTEGER SPEED SET. So partition speed
sets, not reading types.  The framework's own splitting objects, in order:

  (a) does the reduced speed set contain 1?   -> integer readings vs rational readings
  (b) is any reading = 0 mod 8?               -> Branch A vs Branch B   (the collision)
  (c) reflection centre: all moduli good / all obstructed / mixed

Measure the sizes, so the map is quantitative.
"""
from itertools import combinations
from math import gcd
from functools import reduce
from collections import Counter
import random

def good(b): return b % 8 not in (0, 1)

rng = random.Random(20260919)
cat = Counter(); tot = 0
for _ in range(400000):
    A = sorted(rng.sample(range(1, 400), 7))
    g = reduce(gcd, A)
    red = [a // g for a in A]
    dmin = min(red)
    readings = [a / dmin for a in red]
    tot += 1
    has_unit = (1 in red)                                   # (a)
    if not has_unit:
        cat['rational readings (no unit speed)'] += 1
        continue
    ints = [a // dmin for a in red]                          # dmin = 1 here
    collide = any(s % 8 == 0 for s in ints)                  # (b)
    if not collide:
        cat['A: integer readings, no collider'] += 1
        continue
    m = max(ints)
    divclosed = all(m % s == 0 for s in ints)
    cat['B: integer readings, collider' + (' [divisor-closed]' if divclosed else '')] += 1
print(f"random integer speed sets at n = 8 : {tot:,}\n")
for k, v in sorted(cat.items(), key=lambda kv: -kv[1]):
    print(f"   {k:<44} {v:>8,}  ({100*v/tot:5.2f}%)")
print()
print("   NOTE: 'real / irrational' is NOT a category -- the classical reduction sends every")
print("   instance to an integer speed set, so it cannot be a sibling of the others.")
