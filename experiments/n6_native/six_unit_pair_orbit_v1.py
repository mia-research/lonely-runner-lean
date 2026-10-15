#!/usr/bin/env python3
"""Divisible-largest residual sets (e = 6E unique multiple of 6). Unit pair d1 = 1 mod 6, d5 = 5 mod 6,
with q = d // 6. The coarse-shift-invariant quantity is sigma(i) = a1(i) + a5(i) mod 6. Its driver is
the 1-D orbit i -> 6*((Q+1)*i mod E) with Q = q1 + q5, of length L = E / gcd(Q+1, E).
For each set: is sigma = 5 reached (unit-pair forcing)?  Tabulate against L (orbit length)."""
import sys, math, importlib.util
from itertools import combinations
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1])
tab = Counter(); missed = []
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    e = S[-1]
    if not (e % 6 == 0 and sum(d % 6 == 0 for d in S) == 1): continue
    E = e // 6; rest = S[:-1]
    d1 = [d for d in rest if d % 6 == 1]; d5 = [d for d in rest if d % 6 == 5]
    d1, d5 = d1[0], d5[0]
    q1, q5 = d1 // 6, d5 // 6
    Q = q1 + q5; L = E // math.gcd(Q + 1, E)
    hit = any(((((d1 * i + q1) % (6 * E)) // E) + (((d5 * i + q5) % (6 * E)) // E)) % 6 == 5 for i in range(E))
    tab[(min(L, 6), hit)] += 1
    if not hit and len(missed) < 8: missed.append((S, E, Q, L))
print(f"HI={HI}: (orbit length L capped at 6, unit pair reaches sigma=5) -> sets")
for k in sorted(tab): print("  ", k, tab[k])
print("  examples missed:", missed)
