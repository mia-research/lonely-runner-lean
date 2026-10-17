#!/usr/bin/env python3
"""Provable split chain (o7_split_an_v1: native-order windows, single-runner gap, stretch recursion; EXACT Fractions,
formula-only) on random primitive prefixes with v5 > 100 v1 (the region below the Lean tree x1 >= 1/100).
Not closed ones are classified by the smallest consecutive ratio inside the fast block of each split (cluster test)."""
import math, random, sys
from fractions import Fraction as Fr
from collections import Counter
from o7_split_an_v1 import closes
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
N = int(sys.argv[1]); c = Counter(); bad = []
while sum(c.values()) < N:
    v1 = random.randint(1, 6); v5 = random.randint(100 * v1 + 1, 2000)
    mid = sorted(random.sample(range(v1 + 1, v5), 3)); P = (v1, *mid, v5)
    if math.gcd(*P) != 1: continue
    j = closes(P); c[j] += 1
    if j == 0 and len(bad) < 40: bad.append(P)
n = sum(c.values())
print(f"exact provable split chain, {n} random primitive prefixes with v5 > 100 v1: closed {n - c[0]} ({(n - c[0]) / n:.2%}); by split {dict(sorted(c.items()))}")
rat = Counter()
for P in bad:
    r = min(Fr(P[i + 1], P[i]) for i in range(1, 4))
    rat[min(int(r * 4) / 4, 3)] += 1
print("   not closed (first 40): smallest consecutive ratio among v2..v5, bins of 1/4:", sorted(rat.items()))
print("   examples:", bad[:15])
