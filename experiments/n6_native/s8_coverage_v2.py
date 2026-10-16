#!/usr/bin/env python3
"""Coverage of §8 (primitive 5-sets <= H, v3 <= 3 v1) by the finite list of proved statements (S8Windows_v2):
  W3: block3_window_laps on laps (0,0,0), (1,2,3), (0,1,1), (0,0,1) (window_two's base and residue conditions);
  F4: block4_fold_laps on laps (0,0,0,0);
  B : box5 on lap vectors (0,0,0,0,0) (spread), (0,0,0,0,1) (runner-5 second lap), (0,0,0,1,1), (0,0,1,1,2), (0,1,2,3,4).
Per statement: sets it closes first (in the order listed); the remainder with its ratio ranges v_i/v1 and examples;
and how many of the remainder a 4-block fold on laps (1,2,3,4), (0,1,2,3), (0,1,1,1), (0,0,1,1) would close."""
import math, sys
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
H = int(sys.argv[1]) if len(sys.argv) > 1 else 40
def win(S, laps):
    L = max(F(6 * m + 1, 6 * v) for v, m in zip(S, laps)); U = min(F(6 * m + 5, 6 * v) for v, m in zip(S, laps))
    return (L, U) if L <= U else None
def sharp(l, a, b):
    if l < F(1, 3 * a) + F(1, 3 * b): return False
    m = 0
    while 3 * m * a < a + b:
        if F(3 * m + 1, 3 * b) > l: return False
        m += 1
    return True
def box(S, k): return all((6 * k[i] + 1) * S[j] <= (6 * k[j] + 5) * S[i] for i in range(5) for j in range(5))
W3 = [(0, 0, 0), (1, 2, 3), (0, 1, 1), (0, 0, 1)]
BX = [(0, 0, 0, 0, 0), (0, 0, 0, 0, 1), (0, 0, 0, 1, 1), (0, 0, 1, 1, 2), (0, 1, 2, 3, 4)]
F4x = [(1, 2, 3, 4), (0, 1, 2, 3), (0, 1, 1, 1), (0, 0, 1, 1)]
c = Counter(); rest = []; N = 0
for S in combinations(range(1, H + 1), 5):
    v1, v2, v3, v4, v5 = S
    if v3 > 3 * v1 or math.gcd(*S) != 1: continue
    N += 1; done = None
    for laps in W3:
        w = win(S[:3], laps)
        if w and sharp(w[1] - w[0], v4, v5): done = f"W3 {laps}"; break
    if not done:
        w = win(S[:4], (0, 0, 0, 0))
        if w and v5 * (w[1] - w[0]) >= F(1, 3): done = "F4 (0,0,0,0)"
    if not done:
        for k in BX:
            if box(S, k): done = f"box {k}"; break
    if done: c[done] += 1
    else: rest.append(S)
print(f"H={H}: §8 primitive sets {N}; closed {N - len(rest)}; remaining {len(rest)}")
for k, n in sorted(c.items(), key=lambda z: -z[1]): print(f"   {n:8d}  {k}")
if rest:
    for i in range(1, 5):
        xs = [F(s[i], s[0]) for s in rest]; print(f"   remaining v{i+1}/v1 in [{min(xs)}, {max(xs)}] (~{float(min(xs)):.3f}..{float(max(xs)):.3f})")
    print("   examples:", rest[:12])
    more = sum(1 for S in rest if any((w := win(S[:4], k)) and S[4] * (w[1] - w[0]) >= F(1, 3) for k in F4x))
    print(f"   of these, closed by a 4-block fold on laps {F4x}: {more}")
