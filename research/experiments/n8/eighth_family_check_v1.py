"""Independent check of the eighth-family claims (exact rationals).

Family, scale-normalised to d_max = 8:  D(x) = {1, 3, 4, 5, 7, x, 8},  0 < x < 8.
Flank at difference 7; its k-th opening is t = (k + 1/8)/7, where a difference d sits at d(k + 1/8)/7.
Threshold 1/8; clear means circDist >= 1/8 (zones are OPEN, so equality is clear).

Checks: (1) which residues k mod 7 leave all six fixed differences clear; (2) the claim in
EIGHTH_FAMILY_v1's proof paragraph that k = 1 serves every integer x; (3) the theorem for integer x;
(4) the theorem for random non-integer rationals; (5) that the phase step reduces to frac(x), which is
what lets Flanks.exists_clear_step close the non-integer case with no density argument.
"""
from fractions import Fraction as F
import random
TH = F(1, 8)
def cd(x):
    f = x % 1
    return min(f, 1 - f)
def clear(d, k):
    return cd(F(d) * (k + TH) / 7) >= TH
FIXED = [1, 3, 4, 5, 7, 8]
print("1. residues k mod 7 with all six fixed differences clear")
free = []
for k in range(7):
    bad = [d for d in FIXED if not clear(d, k)]
    print(f"   k={k}: {'ALL CLEAR' if not bad else 'blocked by ' + str(bad)}")
    if not bad: free.append(k)
print(f"   -> {free}   (v1 claims 1, 3)")
print("\n2. v1's proof paragraph: 'integer x: k = 1 is free outright'")
for x in range(1, 8):
    c1, c3 = clear(x, 1), clear(x, 3)
    print(f"   x={x}: k=1 {'clear' if c1 else 'BLOCKED'}, k=3 {'clear' if c3 else 'blocked'}"
          + ("   <-- refutes the paragraph" if not c1 else ""))
print("\n3. theorem, integer x: some k in {1,3} fully clear")
for x in range(1, 8):
    ok = [k for k in (1, 3) if all(clear(d, k) for d in FIXED + [x])]
    print(f"   x={x}: k={ok}" if ok else f"   x={x}: FAILS")
print("\n4. theorem, 4000 random non-integer rationals")
rng = random.Random(7); fails = 0; worst = None
for _ in range(4000):
    b = rng.randint(2, 40); a = rng.randint(1, 8 * b - 1); x = F(a, b)
    if x.denominator == 1 or not (0 < x < 8): continue
    found = None
    for j in range(60):
        for r in (1, 3):
            if all(clear(d, r + 7 * j) for d in FIXED + [x]): found = (r + 7 * j, j); break
        if found: break
    if found is None: fails += 1; print(f"   FAIL x={x}")
    elif worst is None or found[1] > worst[1]: worst = (x, found[1], found[0])
print(f"   failures: {fails}; largest j needed: x={worst[0]}, j={worst[1]}, k={worst[2]}")
print("\n5. phase step reduces to frac(x)  (so exists_clear_step applies; no density needed)")
for x in [F(22, 7), F(13, 5), F(1, 3), F(45, 8)]:
    base = F(9, 56) * x
    same = all(cd(base + j * x) == cd(base + j * (x % 1)) for j in range(25))
    print(f"   x={x}: circDist(base + j*x) == circDist(base + j*frac(x)) for j < 25: {same}")
