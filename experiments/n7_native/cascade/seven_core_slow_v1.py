#!/usr/bin/env python3
"""Cascade-order reading (A first instant, B 1/7 grid, C 7-divisible flank cell, D other) on random primitive six-sets
in the region v6 > 100 v1 (EXACT).  For D: the phase-1 window class (o7_exact) and the rank of the multiple(s) of 7."""
import sys, math, random
sys.path.insert(0, "..")
from collections import Counter
from seven_core_v1 import closer
from o7_exact import classify
rnd = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1); N = int(sys.argv[1])
c = Counter(); dcls = Counter(); dpos = Counter(); ex = []
n = 0
while n < N:
    v1 = rnd.randint(1, 12); v6 = rnd.randint(101 * v1, 1200 * v1)
    S = (v1, *sorted(rnd.sample(range(v1 + 1, v6), 4)), v6)
    if math.gcd(*S) != 1: continue
    n += 1; k = closer(S); c[k] += 1
    if k == "D":
        cl = classify(S)[0]; dcls[cl] += 1
        dpos[tuple(i + 1 for i, d in enumerate(S) if d % 7 == 0)] += 1
        if len(ex) < 10: ex.append((S, cl))
print(f"{N} random sets with v6 > 100 v1: first closer {dict(sorted(c.items()))}")
print("  D: window class", dict(dcls), "; ranks of multiples of 7", sorted(dpos.items()))
print("  D examples:", ex)
