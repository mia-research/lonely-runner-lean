#!/usr/bin/env python3
"""Service-state transfer from n=11 (blocking grammar §11.7-§13): find a small set L of instants (all allowed by
runner 1) such that the blocked traces of the abstract unit states on L admit no cover of L by four traces.
Exact; cover check by superset-OR (SOS) over pair unions.  Usage: seven_trace_search_v1.py size trials seed"""
import sys, random
import numpy as np
exec(open("seven_abstract_v1.py").read().split("units49 =")[0].replace("CMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6", "CMAX = 6"))
units49 = [r for r in range(1, 49) if r % 7]
NS = len(strategies)
allowed1 = [b for b, (c, s) in enumerate(strategies) if 7 <= (c * 0 + 0 + s * c * 1) % 49 <= 41]
masks = sorted({mask(T, fl, rho) for T in range(49) for fl in FL for rho in units49})
B = np.array([[not (m >> b & 1) for b in range(NS)] for m in masks], dtype=bool)  # blocked
def traces(L):
    sub = B[:, L]
    w = (sub * (1 << np.arange(len(L)))).sum(axis=1)
    t = np.unique(w)
    # keep maximal
    t = sorted(t.tolist(), key=lambda x: -bin(x).count("1"))
    mx = []
    for x in t:
        if not any((x | y) == y for y in mx): mx.append(x)
    return mx
def coverable(mx, n):
    full = (1 << n) - 1
    f = np.zeros(1 << n, dtype=bool)
    arr = np.array(mx, dtype=np.int64)
    pu = np.unique((arr[:, None] | arr[None, :]).ravel())
    f[pu] = True
    g = f.copy()  # g[S] = some pair-union is a superset of S
    for i in range(n):
        bit = 1 << i
        idx = np.arange(1 << n)
        sel = (idx & bit) == 0
        g[idx[sel]] |= g[idx[sel] | bit]
    need = full & ~pu
    return bool(g[need].any())
size, trials, seed = map(int, sys.argv[1:4])
rng = random.Random(seed)
found = 0
for tr in range(trials):
    L = sorted(rng.sample(allowed1, size))
    mx = traces(L)
    if not coverable(mx, size):
        found += 1
        print("COVER-FREE", L, "maximal traces", len(mx), [strategies[b] for b in L])
        if found >= 3: break
print(f"size {size}: {trials} trials, cover-free found {found}; last maximal traces {len(mx)}")
