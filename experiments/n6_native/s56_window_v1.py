#!/usr/bin/env python3
"""Observation only. BHK §5 (3 v1 < v3, D | v1) and §6 (3 v1 < v3, D | v3, D not | v1), D = v3 - v2; primitive 5-sets
<= H. Statements available as proved lemmas, now with ANY block:
  W: a block of three runners on laps (m), clear on W = [max (m_i+1/6)/v_i, min (m_i+5/6)/v_i]; the other two (a <= b)
     by window_two (base and residue conditions);
  F: a block of four runners on laps, clear on W; the fifth folded alone (v |W| >= 1/3);
  B: a lap box (all five).
For each set: the earliest W or F (by window start, t <= 3/v1) and its (block, laps) type; sets closed by neither.
Then a greedy list of (statement, block, laps) types covering the sets, and how it grows with H."""
import math, sys
from fractions import Fraction as F
from itertools import combinations, product
from collections import Counter
H = int(sys.argv[1]) if len(sys.argv) > 1 else 30
def case(S):
    v1, v2, v3 = S[:3]; D = v3 - v2
    if v3 <= 3 * v1: return None
    if v1 % D == 0: return "S5"
    if v3 % D == 0: return "S6"
    return None
def sharp(l, a, b):
    if l < F(1, 3 * a) + F(1, 3 * b): return False
    m = 0
    while 3 * m * a < a + b:
        if F(3 * m + 1, 3 * b) > l: return False
        m += 1
    return True
def windows(vs, tmax):
    out = []
    def rec(i, L, U, ms):
        if L > U or L > tmax: return
        if i == len(vs): out.append((L, U, tuple(ms))); return
        for m in range(int(L * vs[i]), int(tmax * vs[i]) + 1):
            rec(i + 1, max(L, F(6 * m + 1, 6 * vs[i])), min(U, F(6 * m + 5, 6 * vs[i])), ms + [m])
    rec(0, F(0), F(10 ** 9), []); return out
def types_closing(S):
    tmax = F(3, S[0]); res = []
    for blk in combinations(range(5), 3):
        rest = [i for i in range(5) if i not in blk]
        a, b = S[rest[0]], S[rest[1]]
        for L, U, ms in windows([S[i] for i in blk], tmax):
            if sharp(U - L, a, b): res.append(("W", blk, ms))
    for blk in combinations(range(5), 4):
        r = [i for i in range(5) if i not in blk][0]
        for L, U, ms in windows([S[i] for i in blk], tmax):
            if S[r] * (U - L) >= F(1, 3): res.append(("F", blk, ms))
    return res
sets = [S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and case(S)]
cnt = Counter(case(S) for S in sets)
cov = {S: set(types_closing(S)) for S in sets}
none = [S for S in sets if not cov[S]]
print(f"H={H}: §5 {cnt['S5']}, §6 {cnt['S6']}; closed by some W or F (t <= 3/v1): {len(sets) - len(none)}; neither: {len(none)}", none[:12])
left = set(S for S in sets if cov[S]); greedy = []
allt = Counter(t for S in left for t in cov[S])
while left:
    t = max(allt, key=lambda z: sum(1 for S in left if z in cov[S]))
    hit = {S for S in left if t in cov[S]}
    if not hit: break
    greedy.append((t, len(hit))); left -= hit
print(f"greedy list of statement types: {len(greedy)}")
for t, n in greedy[:25]: print("   ", n, t)
