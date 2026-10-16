#!/usr/bin/env python3
"""§6 coverage by the two proved theorems: s6_meeting_uniform (4 v2 v3 <= v4 (5 v2 - v3)) and s6_generic
(gcd(v1, D) = 1, D >= 15, direction lam = v4 * v1^{-1} mod D with 2 <= |lam| <= D/2 as a representative in
(-D/2, D/2]); the rest by reason: D < 15, gcd(v1, D) > 1, lam in {0, +-1}."""
import math, sys, random
from itertools import combinations
from collections import Counter
def s6(S):
    v1, v2, v3 = S[:3]; D = v3 - v2
    return v3 > 3 * v1 and v3 % D == 0 and v1 % D != 0
def classify(S):
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    if 4 * v2 * v3 <= v4 * (5 * v2 - v3): return "uniform (proved)"
    if math.gcd(v1, D) != 1: return "rest: gcd(v1,D) > 1"
    lam = v4 * pow(v1, -1, D) % D
    if lam > D // 2: lam -= D
    if D >= 15 and 2 <= abs(lam) and 2 * abs(lam) <= D: return "generic (proved)"
    if D < 15: return "rest: D < 15"
    return f"rest: lam = {lam}"
def run(sets, label):
    c = Counter(classify(S) for S in sets)
    print(f"{label}: {len(sets)} §6 sets:", dict(sorted(c.items(), key=lambda z: -z[1])))
H = int(sys.argv[1]) if len(sys.argv) > 1 else 40
run([S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and s6(S)], f"§6 <= {H}")
random.seed(6); big = []
while len(big) < 3000:
    S = tuple(sorted(random.sample(range(1, 3001), 5)))
    if math.gcd(*S) == 1 and s6(S): big.append(S)
run(big, "random §6 <= 3000")
