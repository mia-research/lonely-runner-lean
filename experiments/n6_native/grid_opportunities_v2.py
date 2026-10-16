#!/usr/bin/env python3
"""Observation only; follow-up to grid_opportunities_v1. Does q* (least grid q with a lonely unit instant c/q) stay small
as speeds grow? (a) all primitive SixResidual sets <= 40 by max entry; (b) random primitive SixResidual sets with
entries <= H for H = 80, 160, 320 (seeded sample, sizes stated); (c) random primitive 5-sets (any, not only residual)
with entries <= 1000."""
import random, math
from collections import Counter, defaultdict
import importlib.util
sp = importlib.util.spec_from_file_location("r", "six_residual_v1.py"); r = importlib.util.module_from_spec(sp); sp.loader.exec_module(r)
def blocks(d, c, q): x = (d * c) % q; return 6 * x < q or 6 * x > 5 * q
def qstar(S):
    q = 2
    while True:
        if any(math.gcd(c, q) == 1 and not any(blocks(d, c, q) for d in S) for c in range(1, q)): return q
        q += 1
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
bymax = defaultdict(int)
for S in rows: bymax[S[-1] // 10] = max(bymax[S[-1] // 10], qstar(S))
print("(a) largest q* among SixResidual sets with max entry in [10j, 10j+9]:", dict(sorted(bymax.items())))
random.seed(20261016)
for H in (80, 160, 320):
    got = Counter(); n = 0; tries = 0
    while n < 400 and tries < 3_000_000:
        tries += 1
        S = tuple(sorted(random.sample(range(1, H + 1), 5)))
        if math.gcd(*S) != 1 or not r.six_residual(S): continue
        n += 1; got[qstar(S)] += 1
    print(f"(b) H={H}: {n} residual sets sampled ({tries} draws); q* distribution:", sorted(got.items()), "max", max(got))
got = Counter()
for _ in range(20000):
    S = tuple(sorted(random.sample(range(1, 1001), 5)))
    if math.gcd(*S) != 1: continue
    got[qstar(S)] += 1
print("(c) random primitive 5-sets <= 1000:", sorted(got.items()), "max", max(got))
