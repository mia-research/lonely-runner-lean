#!/usr/bin/env python3
"""Exact (integer masks): can r units fail at level a (no unit k mod 7^a with every u k mod 7^a in [7^(a-1), 6 7^(a-1)])?
Random sampling, then hill climbing on the popcount of the common mask.  Usage: seven_level4_units_v1.py a r trials seed"""
import sys, random
a, r, trials, seed = map(int, sys.argv[1:5])
N = 7 ** a; lo, hi = 7 ** (a - 1), 6 * 7 ** (a - 1)
units = [u for u in range(1, N) if u % 7]
ks = units
mask = {}
for u in units:
    m = 0
    for b, k in enumerate(ks):
        x = u * k % N
        if lo <= x <= hi: m |= 1 << b
    mask[u] = m
rng = random.Random(seed)
def common(t):
    m = mask[1]
    for u in t: m &= mask[u]
    return m
fails = []
best = None
for tr in range(trials):
    t = [rng.choice(units) for _ in range(r - 1)]
    c = bin(common(t)).count("1")
    for step in range(400):
        i = rng.randrange(r - 1); old = t[i]; t[i] = rng.choice(units)
        c2 = bin(common(t)).count("1")
        if c2 <= c: c = c2
        else: t[i] = old
        if c == 0: break
    if best is None or c < best[0]: best = (c, sorted(t))
    if c == 0: fails.append(sorted(t))
print(f"level {a}, {r} units (1 fixed), {trials} climbs: failures {len(fails)}; best {best}")
for f in fails[:5]: print("  fail (1,) +", f)
