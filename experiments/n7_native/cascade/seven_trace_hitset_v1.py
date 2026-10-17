#!/usr/bin/env python3
"""Lazy hitting set for the five-unit abstract claim (service-state transfer from n=11): grow an instant set L
(allowed by runner 1) until the blocked traces on L admit no 4-cover.  Each round finds a covering 4-tuple of
traces (exact, superset-OR over pair unions), maps it to actual states, and adds one of that tuple's good instants
(nonempty by E24).  Usage: seven_trace_hitset_v1.py seed maxsize"""
import sys, random
import numpy as np
exec(open("seven_abstract_v1.py").read().split("units49 =")[0].replace("CMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6", "CMAX = 6"))
units49 = [r for r in range(1, 49) if r % 7]
NS = len(strategies)
m1 = mask(0, FL[0], 1)
allowed1 = [b for b in range(NS) if m1 >> b & 1]
masks = sorted({mask(T, fl, rho) for T in range(49) for fl in FL for rho in units49})
G = np.array([[bool(m >> b & 1) for b in range(NS)] for m in masks], dtype=bool)  # good
seed, maxsize = int(sys.argv[1]), int(sys.argv[2])
rng = random.Random(seed)
L = sorted(rng.sample(allowed1, 8))
def find_cover(L):
    n = len(L)
    blocked = ~G[:, L]
    w = (blocked * (1 << np.arange(n))).sum(axis=1).astype(np.int64)
    rep = {}
    for i, x in enumerate(w.tolist()): rep.setdefault(x, i)
    t = sorted(rep, key=lambda x: -bin(x).count("1"))
    mx = []
    for x in t:
        if not any((x | y) == y for y in mx): mx.append(x)
    arr = np.array(mx, dtype=np.int64)
    pu = (arr[:, None] | arr[None, :])
    full = (1 << n) - 1
    f = np.full(1 << n, -1, dtype=np.int64)  # f[S] = index of a pair union equal to S (flattened)
    flat = pu.ravel()
    f[flat] = np.arange(flat.size)
    g = f.copy()
    idx = np.arange(1 << n)
    for i in range(n):
        bit = 1 << i
        sel = idx[(idx & bit) == 0]
        upd = g[sel | bit]
        g[sel] = np.where(g[sel] >= 0, g[sel], upd)
    need = full & ~flat
    hit = np.nonzero(g[need] >= 0)[0]
    if hit.size == 0: return None, len(mx)
    p = hit[0]; q = g[need[p]]
    a, b = divmod(int(p), len(mx)); c, d = divmod(int(q), len(mx))
    return [rep[mx[a]], rep[mx[b]], rep[mx[c]], rep[mx[d]]], len(mx)
while len(L) <= maxsize:
    tup, nmx = find_cover(L)
    if tup is None:
        print("COVER-FREE instant set of size", len(L), "maximal traces", nmx)
        print("L =", L); print("instants (c,s) =", [strategies[b] for b in L]); break
    good = G[tup[0]] & G[tup[1]] & G[tup[2]] & G[tup[3]]
    cand = [b for b in allowed1 if good[b] and b not in L]
    assert cand, "full problem would be covered"
    # prefer the candidate that is good for the most states (blocks least)
    b = max(cand, key=lambda b: (G[:, b].sum(), rng.random()))
    L = sorted(L + [b])
    print(f"size {len(L)}: added {strategies[b]}, traces {nmx}", flush=True)
else:
    print("no cover-free set up to", maxsize)
