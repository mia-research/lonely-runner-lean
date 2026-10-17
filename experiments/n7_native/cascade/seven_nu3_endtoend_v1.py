#!/usr/bin/env python3
"""Exact end-to-end check of the claim: a set of six speeds with nu_max = nu >= 3 (and a unit present) is in band at
some unit instant of level nu + 1.  Hill climbing on the number of good k, over random valuation shapes."""
import random, sys
nu, climbs, seed = map(int, sys.argv[1:4])
a = nu + 1; N = 7 ** a; lo, hi = N // 7, 6 * N // 7
ks = [k for k in range(1, N) if k % 7]
rng = random.Random(seed)
def rand_val(v):
    while True:
        m = rng.randrange(1, N // 7 ** v + 1)
        if m % 7: return 7 ** v * m % N or 7 ** v
def good(S): return sum(all(lo <= d * k % N <= hi for d in S) for k in ks)
worst = None; fails = []
for c in range(climbs):
    vals = [0] + [rng.choice(range(nu + 1)) for _ in range(4)] + [nu]
    S = [rand_val(v) for v in vals]
    g = good(S)
    for step in range(150):
        i = rng.randrange(6); old = S[i]
        S[i] = rand_val(vals[i]) if rng.random() < 0.5 else (old + 7 ** (vals[i] + rng.randrange(1, a - vals[i] + 1 if vals[i] < a - 1 else 2))) % N or old
        if S[i] % 7 ** vals[i] or (S[i] // 7 ** vals[i]) % 7 == 0: S[i] = old
        g2 = good(S)
        if g2 <= g: g = g2
        else: S[i] = old
        if g == 0: break
    if worst is None or g < worst[0]: worst = (g, sorted(vals), sorted(S))
    if g == 0: fails.append((sorted(vals), sorted(S)))
print(f"nu={nu} level {a}: {climbs} climbs, failures {len(fails)}, worst {worst}")
for f in fails[:5]: print("  FAIL", f)
