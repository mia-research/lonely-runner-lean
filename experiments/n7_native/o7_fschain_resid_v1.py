#!/usr/bin/env python3
"""Residue of the provable first-stretch chain (o7_fschain_v1, EXACT): for unclosed sets with v6 > 100 v1, the terminal
non-lacunary block (maximal run at the fast end with consecutive ratios < 12/5), its size, its largest internal ratio,
its smallest consecutive ratio (cluster test: < 1.05), and its separation Lambda = (block min speed) * (length of the
slow window the chain delivers just before it, using full stretches)."""
import math, random, sys
from fractions import Fraction as Fr
from collections import Counter
from o7_fschain_v1 import chain
rnd = random.Random(7)
size = Counter(); rmin = Counter(); lam = Counter(); n = 0; ex = []
while n < 3000:
    v1 = rnd.randint(1, 20); v6 = rnd.randint(101 * v1, 3000 * v1)
    P = (v1, *sorted(rnd.sample(range(v1 + 1, v6), 4)), v6)
    if math.gcd(*P) != 1 or chain(P): continue
    n += 1
    j = 5
    while j > 1 and Fr(P[j], P[j - 1]) < Fr(12, 5): j -= 1
    B = P[j:]; size[len(B)] += 1
    r = min(Fr(B[i + 1], B[i]) for i in range(len(B) - 1)) if len(B) > 1 else None
    rmin["cluster(<1.05)" if r is not None and r < Fr(21, 20) else "moderate"] += 1
    Lam = Fr(B[0] * 5, 7 * P[j - 1])
    lam[min(int(math.log10(float(Lam))), 4)] += 1
    if len(ex) < 8: ex.append((P, len(B), round(float(B[-1] / B[0]), 2), round(float(Lam), 1)))
print("3000 unclosed random sets (v6 > 100 v1): terminal block size", sorted(size.items()),
      "; smallest internal ratio", dict(rmin), "; log10 separation", sorted(lam.items()))
print("   examples (set, block size, block spread, separation):", ex)
