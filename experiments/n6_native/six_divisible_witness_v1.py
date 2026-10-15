#!/usr/bin/env python3
"""Divisible-largest case (largest e = 6E is the unique multiple of 6) of primitive SixResidual:
(1) the residue patterns mod 6 of the other four elements;
(2) where the good openings j < e sit, as (j // E, j mod E), and the least good j;
(3) whether a good opening exists with j // E in a fixed small set.
Exact integers."""
import sys, math, importlib.util
from itertools import combinations
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1])
pat = Counter(); quot = Counter(); n = 0; least_quot = Counter(); jmodE_zero = 0
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    e = S[-1]
    if not (e % 6 == 0 and sum(d % 6 == 0 for d in S) == 1): continue
    n += 1; E = e // 6
    pat[tuple(sorted(d % 6 for d in S[:-1]))] += 1
    good = [j for j in range(e) if all(e <= (d * (6*j+1)) % (6*e) <= 5*e for d in S)]
    if not good: continue
    least_quot[(good[0] // E) if E > 0 else 0] += 1
    for j in good: quot[j // E] += 1
    if any(j % E == 0 for j in good): jmodE_zero += 1
print(f"HI={HI}: divisible-largest residual sets = {n}")
print("  residue patterns mod 6 of the other four:", dict(pat))
print("  quotient j//E of the least good opening:", dict(sorted(least_quot.items())))
print("  quotient j//E over all good openings:", dict(sorted(quot.items())))
print(f"  sets with a good opening on the coarse grid j = uE: {jmodE_zero}")
