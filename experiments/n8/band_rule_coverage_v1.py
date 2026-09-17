"""Coverage of the Lean rule exists_lonely_of_bands, encoded from its HYPOTHESIS.

  exists_lonely_of_bands: some e in ds and k with, for every d in ds, an integer M such that
      n*M + 1  <=  (d/e) * (n*k + 1)  <=  n*M + n - 1

First: is that band condition EQUIVALENT to the clearing condition circDist(d * opening) >= 1/n,
or only sufficient? If it were merely sufficient the coverage figures would overstate the rule.
"""
import random
from fractions import Fraction as F
from math import floor

n = 8

def circd(x):
    f = x - (x.numerator // x.denominator)
    return min(f, 1 - f)

def clears(d, e, k):
    return circd(d * (F(k) + F(1, n)) / e) >= F(1, n)

def in_band(d, e, k):
    x = (d / e) * (n * k + 1)
    M = (x - 1) / n
    for cand in (int(floor(M)) - 1, int(floor(M)), int(floor(M)) + 1):
        if n * cand + 1 <= x <= n * cand + n - 1:
            return True
    return False

rng = random.Random(20260917)
agree = tot = 0
mismatch = []
for _ in range(60000):
    e = F(rng.randint(1, 5000), 100)
    d = F(rng.randint(1, 200000), 100)
    k = rng.randint(0, 40)
    tot += 1
    a, b = clears(d, e, k), in_band(d, e, k)
    if a == b: agree += 1
    else: mismatch.append((d, e, k, a, b))
print(f"band condition vs clearing condition, {tot} random (d, e, k):")
print(f"  agree    : {agree}")
print(f"  disagree : {len(mismatch)}")
if mismatch:
    for d, e, k, a, b in mismatch[:4]:
        print(f"    d={d} e={e} k={k}  clears={a} band={b}")
else:
    print("  -> the band hypothesis is EXACTLY the clearing condition, not a weakening,")
    print("     so the rule decides every case the criterion decides.")
