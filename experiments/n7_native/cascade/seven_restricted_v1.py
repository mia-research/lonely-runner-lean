#!/usr/bin/env python3
"""Exact.  Five units (u1 = 1) at level a.  Restricted instants k = c (1 + 7^(a-b) s): c a unit <= C, s in Z/7^b
(the H_b fold, additive when a >= 2b).  Hill-climb for tuples where no restricted instant works, then report
their 7-adic cluster structure (valuations of pairwise differences).  Usage: a b C climbs seed"""
import sys, random
a, b, C, climbs, seed = map(int, sys.argv[1:6])
N = 7 ** a; lo, hi = N // 7, 6 * N // 7
cs = [c for c in range(1, C + 1) if c % 7]
ks = sorted({c * (1 + 7 ** (a - b) * s) % N for c in cs for s in range(7 ** b)})
def ngood(t):
    return sum(all(lo <= u * k % N <= hi for u in t) for k in ks)
def nu(x):
    v = 0
    while x % 7 == 0 and v < a: x //= 7; v += 1
    return v
rng = random.Random(seed)
units = lambda: rng.choice([x for x in (rng.randrange(1, N),) if x % 7] or [1])
fails = []
for _ in range(climbs):
    t = [1] + [0] * 4
    for i in range(1, 5):
        while t[i] % 7 == 0: t[i] = rng.randrange(1, N)
    g = ngood(t)
    for step in range(300):
        i = rng.randrange(1, 5); old = t[i]
        x = 0
        while x % 7 == 0: x = rng.randrange(1, N) if rng.random() < 0.5 else (old + rng.choice([-1, 1]) * 7 ** rng.randrange(0, a)) % N
        t[i] = x
        g2 = ngood(t)
        if g2 <= g: g = g2
        else: t[i] = old
        if g == 0: break
    if g == 0:
        full = sum(all(lo <= u * k % N <= hi for u in t) for k in range(1, N) if k % 7)
        vals = sorted(nu((t[i] - t[j]) % N) for i in range(5) for j in range(i + 1, 5))
        fails.append((sorted(t), full, vals))
print(f"a={a} b={b} C={C}: {len(ks)} restricted instants; {climbs} climbs; restricted failures {len(fails)}")
for f in fails[:12]: print("  ", f[0], "full-group good", f[1], "pair valuations", f[2])
