#!/usr/bin/env python3
"""Provable first-stretch chain for FS100 (EXACT Fractions, formula-only).  Start: runner 1's first stretch, a window of
length l0 = 5/(7 v1) with runner 1 in band.  Process v2..v6 slow to fast in consecutive blocks; a block passes from a
window of length l (position unknown, worst case) to a window of length l' for the processed runners:
  single runner u:   l' = 5/(7u) if l >= 12/(7u) (full stretch, `full_stretch_in`), else (l u - 2/7)/(2u) if positive
  block B, |B| <= 3: union bound with window w: l' = w = (l/7 - sum 4/(7d)) / (2|B| + l sum d)  if positive
  last block:        instant suffices: single runner needs l >= 2/(7u) (`hit_in`); block needs l >= 5 sum 1/d (`gap_three`)
Best over all partitions into blocks.  Reports coverage on samples with v6 > 100 v1 by family."""
import math, random, sys
from fractions import Fraction as Fr
from collections import Counter
from functools import lru_cache
def step(l, B, last):
    if last:
        if len(B) == 1: return Fr(0) if l >= Fr(2, 7 * B[0]) else None
        return Fr(0) if l >= 5 * sum(Fr(1, d) for d in B) else None
    if len(B) == 1:
        u = B[0]
        if l >= Fr(12, 7 * u): return Fr(5, 7 * u)
        x = (l * u - Fr(2, 7)) / (2 * u)
        return x if x > 0 else None
    num = l / 7 - sum(Fr(4, 7 * d) for d in B); den = 2 * len(B) + l * sum(B)
    w = num / den
    return w if w > 0 else None
def chain(P):
    R = P[1:]
    @lru_cache(maxsize=None)
    def best(i, l):
        if i == len(R): return True
        for k in (1, 2, 3):
            if i + k > len(R): break
            l2 = step(l, R[i:i + k], i + k == len(R))
            if l2 is not None and best(i + k, l2): return True
        return False
    return best(0, Fr(5, 7 * P[0]))
rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 4)
res = Counter(); bad = {}
def test(name, P):
    if len(set(P)) < 6 or list(P) != sorted(P) or math.gcd(*P) != 1 or P[5] <= 100 * P[0]: return
    ok = chain(P); res[(name, ok)] += 1
    if not ok: bad.setdefault(name, []).append(P)
for _ in range(4000):   # log-uniform spread
    v1 = rnd.randint(1, 20); top = v1 * rnd.uniform(101, 10**5)
    xs = sorted(math.exp(rnd.uniform(0, math.log(top / v1))) * v1 for _ in range(4))
    test("loguniform", (v1, *[int(x) + 1 + i for i, x in enumerate(xs)], int(top)))
for _ in range(4000):   # uniform middle speeds
    v1 = rnd.randint(1, 20); v6 = rnd.randint(101 * v1, 3000 * v1)
    test("uniform", (v1, *sorted(rnd.sample(range(v1 + 1, v6), 4)), v6))
for _ in range(2000):   # lacunary-ish ratios in [1.5, 4]
    v = [rnd.randint(1, 20)]
    for _ in range(5): v.append(int(v[-1] * rnd.uniform(1.5, 4)) + 1)
    test("ratio1.5-4", tuple(v))
for v1 in range(1, 15):
    for n in (150, 400, 1000, 5000):
        for d in (1, 2, 5, 13):
            test("runs", (v1, n * v1 // max(1, v1) + 0, n + d, n + 2 * d, n + 3 * d, n + 4 * d))
print("provable first-stretch chain, coverage on v6 > 100 v1:", sorted(res.items()))
for k, l in bad.items(): print(f"   {k} not closed, e.g.:", l[:6])
