#!/usr/bin/env python3
"""Observation only; follow-up. The §8 sets left by s8_window_v2 (no 3-block window passing S, no 4-block window folding
runner 5, t <= 3/v1): which are closed by the two proved boxes of E54 — spread box (v5 <= 5 v1, lonely at 1/(6 v1)) and
runner-5 second-lap box (v4 <= 5 v1, 7 v4 <= 5 v5, v5 <= 11 v1) — and what remains. For the remainder: the lap vector
of the cascade's landing (laps of all five), listed."""
import math, sys
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("s8_window_v2.py").read().split("pat = Counter()")[0])
def cd(x): f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def cascade(S):
    t = F(1, 6 * S[0])
    while True:
        b = [d for d in S if cd(d * t) < F(1, 6)]
        if not b: return t
        t = max(F(6 * round(d * t) + 1, 6 * d) for d in b)
kinds = Counter(); rest = []; laps = Counter()
for S in combinations(range(1, H + 1), 5):
    v1, v2, v3, v4, v5 = S
    if v3 > 3 * v1 or math.gcd(*S) != 1: continue
    if any(passS(U - L, v4, v5) for L, U, m in windows(v1, v2, v3, F(3, v1))): continue
    if any(v5 * (U - L) >= F(1, 3) for L, U, m in windows4(S, F(3, v1))): continue
    if v5 <= 5 * v1: kinds["spread box"] += 1; continue
    if v4 <= 5 * v1 and 7 * v4 <= 5 * v5 and v5 <= 11 * v1: kinds["runner-5 second-lap box"] += 1; continue
    kinds["remaining"] += 1; rest.append(S); T = cascade(S); laps[tuple((d * T).numerator // (d * T).denominator for d in S)] += 1
print(f"H={H}:", dict(kinds))
print("remaining sets:", rest[:30])
print("their landing lap vectors:", laps.most_common(10))
