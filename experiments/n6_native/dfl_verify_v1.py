#!/usr/bin/env python3
"""Independent check of a DoorFirstLap witness at order n, without the cascade. By the opening equivalence the
earliest lonely instant of a positive set is an opening (j + 1/n)/b of some element b. Enumerate every opening
of every element with value <= T*, find the earliest lonely one, and compare with the cascade's T*.
Usage: dfl_verify_v1.py n d1 d2 ..."""
import sys, math, importlib.util
from fractions import Fraction as F
n = int(sys.argv[1]); S = tuple(sorted(int(x) for x in sys.argv[2:]))
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
thr = F(1, n)
def lonely(t): return all(cd(d * t) >= thr for d in S)
# cascade
m = min(S); t = F(1, n * m); mv = 0
while not lonely(t):
    t = max((-((-(d * t - thr).numerator) // (d * t - thr).denominator) + thr) / d for d in S if cd(d * t) < thr); mv += 1
Tc = t
# independent: earliest lonely opening
cands = sorted({F(n * j + 1, n * b) for b in S for j in range(int(b * Tc) + 2) if F(n * j + 1, n * b) <= Tc})
first = next(u for u in cands if u > 0 and lonely(u))
print(f"n={n} S={S}: cascade T = {Tc} ({mv} moves); earliest lonely opening by enumeration = {first}; agree: {first == Tc}")
print(f"  tau = d_min * T = {m * Tc} = {float(m * Tc):.5f}; DoorFirstLap (tau <= 1) holds: {m * Tc <= 1}")
print(f"  openings checked: {len(cands)}; gcd = {math.gcd(*S)}")
if n == 6:
    spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
    r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
    print(f"  in SixResidual: {r.six_residual(S)}")
