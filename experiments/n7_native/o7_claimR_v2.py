#!/usr/bin/env python3
"""Claim R, two exact checks.
 (a) First-stretch theorem on integers: every primitive six-set (v1 < ... < v6) <= H has a lonely instant (1/7) in
     [1/(7 v1), 6/(7 v1)] (exact integer bands, o7_exact).
 (b) Claim R for REAL speeds: random rational w (denominators up to 10^4) with min w >= R, five runners, theta in
     [1/7, 6/7]: exact Fraction band intersection on [1/7, 6/7]; also near-resonant w = c Q + small rational offsets."""
import math, random, sys
from fractions import Fraction as Fr
from itertools import combinations
from collections import Counter
from o7_exact import lcm, inter
def first_stretch_int(S):
    M = lcm(S); N = 7 * M; cur = None
    for v in S:
        q = M // v; B = [((7 * m + 1) * q, (7 * m + 6) * q) for m in range(v)]
        cur = B if cur is None else inter(cur, B, strict=False)
    lo, hi = Fr(N, 7 * S[0]), Fr(6 * N, 7 * S[0])
    return any(L <= hi and U >= lo for L, U in cur)
def claimR_real(w):
    S7, S67 = Fr(1, 7), Fr(6, 7)
    cur = [(S7, S67)]
    for x in w:
        B = []
        m = math.floor(x * S7)
        while (m + S7) / x <= S67:
            lo, hi = max((m + S7) / x, S7), min((m + S67) / x, S67)
            if hi >= lo: B.append((lo, hi))
            m += 1
        cur = inter(cur, B, strict=False)
        if not cur: return False
    return True
H = int(sys.argv[1]) if len(sys.argv) > 1 else 30
bad = []
n = 0
for S in combinations(range(1, H + 1), 6):
    if math.gcd(*S) != 1: continue
    n += 1
    if not first_stretch_int(S): bad.append(S)
print(f"(a) primitive six-sets <= {H}: {n}; without a lonely instant in the first stretch of v1: {len(bad)}", bad[:20])
rnd = random.Random(3); c = Counter(); badr = []
for R in (1.5, 2, 3, 5, 10, 30, 100, 1000):
    for _ in range(800):
        w = sorted(Fr(rnd.randint(int(R * 10**4), int(R * 6 * 10**4)), 10**4) for _ in range(5))
        ok = claimR_real(w); c[(R, ok)] += 1
        if not ok and len(badr) < 10: badr.append((R, [float(x) for x in w]))
    for _ in range(400):
        Q = sorted(rnd.sample(range(1, 13), 5)); cc = Fr(rnd.randint(int(R * 10**3), int(R * 10**4)), 10**3) / Q[0]
        w = [cc * q + Fr(rnd.randint(0, 3000), 10**4) for q in Q]
        if min(w) < R: continue
        ok = claimR_real(w); c[(f"res {R}", ok)] += 1
        if not ok and len(badr) < 10: badr.append((f"res {R}", [float(x) for x in w]))
print("(b) real speeds, theta in [1/7, 6/7]:", sorted(c.items(), key=str))
print("   failures:", badr)
