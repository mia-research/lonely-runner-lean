#!/usr/bin/env python3
"""Observation only; follow-up to s8_window_v1. For the §8 sets with no slow-block (runners 1-3) window passing the
two-runner test (S) for t <= 3/v1: use the block of runners 1-4 and fold runner 5 alone. A window W of runners 1-4
(laps m1..m4) closes when v5 |W| >= 1/3 (runner 5 sweeps a third of a lap, so it meets the closed band).
Recorded: the first such window's laps; sets still open (listed)."""
import math, sys
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("s8_window_v1.py").read().split("first = Counter()")[0])
def windows4(S, tmax):
    v = S[:4]; out = []
    def rec(i, L, U, ms):
        if L > U or L > tmax: return
        if i == 4: out.append((L, U, tuple(ms))); return
        for m in range(0, int(tmax * v[i]) + 1):
            rec(i + 1, max(L, F(6 * m + 1, 6 * v[i])), min(U, F(6 * m + 5, 6 * v[i])), ms + [m])
    rec(0, F(0), F(10**9), []); out.sort(); return out
pat = Counter(); still = []; n = 0
for S in combinations(range(1, H + 1), 5):
    v1, v2, v3, v4, v5 = S
    if v3 > 3 * v1 or math.gcd(*S) != 1: continue
    W = windows(v1, v2, v3, F(3, v1))
    if any(passS(U - L, v4, v5) for L, U, m in W): continue
    n += 1
    W4 = windows4(S, F(3, v1))
    hit = next((m for L, U, m in W4 if v5 * (U - L) >= F(1, 3)), None)
    if hit is None: still.append(S)
    else: pat[hit] += 1
print(f"H={H}: §8 sets with no 3-block window passing S: {n}")
print("first 4-block window folding runner 5 (laps):", pat.most_common(10))
print(f"still open: {len(still)}", still[:20])
print("still open, v4/v1 and v5/v1 ranges:", (min(F(s[3], s[0]) for s in still), max(F(s[3], s[0]) for s in still)) if still else None,
      (min(F(s[4], s[0]) for s in still), max(F(s[4], s[0]) for s in still)) if still else None)
