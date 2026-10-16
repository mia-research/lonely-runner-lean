#!/usr/bin/env python3
"""Observation only (candidate 1 of FORMAL_RETHINK_v1). Every primitive 5-set v1<...<v5 <= H with v3 <= 3 v1 (BHK §8).
Slow-block windows: for laps (m1,m2,m3), W = [max (m_i+1/6)/v_i, min (m_i+5/6)/v_i] over runners 1-3 (all clear on W).
Tests on W for runners a = v4, b = v5:
  (U) window_two_uniform: |W| >= 2/(3 v4);
  (S) window_two: |W| >= 1/(3 v4) + 1/(3 v5) and for every integer m with 3 m v4 < v4 + v5: (m + 1/3)/v5 <= |W|.
Recorded: whether the first window (0,0,0) passes (U) / (S); otherwise the first window in time (t <= 3/v1) that passes,
and its laps; sets with no passing window in that range (listed)."""
import math, sys
from fractions import Fraction as F
from itertools import combinations, product
from collections import Counter
H = int(sys.argv[1]) if len(sys.argv) > 1 else 40
def windows(v1, v2, v3, tmax):
    out = []
    for m1 in range(0, int(tmax * v1) + 1):
        for m2 in range(0, int(tmax * v2) + 1):
            for m3 in range(0, int(tmax * v3) + 1):
                L = max(F(6 * m1 + 1, 6 * v1), F(6 * m2 + 1, 6 * v2), F(6 * m3 + 1, 6 * v3))
                U = min(F(6 * m1 + 5, 6 * v1), F(6 * m2 + 5, 6 * v2), F(6 * m3 + 5, 6 * v3))
                if L <= U and L <= tmax: out.append((L, U, (m1, m2, m3)))
    out.sort(); return out
def passU(l, a, b): return l >= F(2, 3 * a)
def passS(l, a, b):
    if l < F(1, 3 * a) + F(1, 3 * b): return False
    m = 0
    while 3 * m * a < a + b:
        if F(3 * m + 1, 3 * b) > l: return False
        m += 1
    return True
first = Counter(); later = Counter(); none = []; N = 0; firstpatU = Counter()
for S in combinations(range(1, H + 1), 5):
    v1, v2, v3, v4, v5 = S
    if v3 > 3 * v1 or math.gcd(*S) != 1: continue
    N += 1
    W = windows(v1, v2, v3, F(3, v1))
    l0 = W[0][1] - W[0][0]; assert W[0][2] == (0, 0, 0)
    u0, s0 = passU(l0, v4, v5), passS(l0, v4, v5)
    first[("first window passes U" if u0 else "first fails U", "passes S" if s0 else "fails S")] += 1
    if not s0:
        hit = next(((L, U, m) for L, U, m in W if passS(U - L, v4, v5)), None)
        if hit is None: none.append(S)
        else: later[hit[2]] += 1
    if not u0:
        hitU = next((m for L, U, m in W if passU(U - L, v4, v5)), None)
        firstpatU[hitU] += 1
print(f"H={H}: §8 primitive sets {N}")
print("first slow-block window [1/(6v1), 5/(6v3)]:", dict(first))
print("when the first fails S: laps of the first window passing S:", later.most_common(10))
print("when the first fails U: laps of the first window passing U:", firstpatU.most_common(10))
print(f"no window passing S with t <= 3/v1: {len(none)}", none[:15])
