#!/usr/bin/env python3
"""(b) Coprime case: primitive SixResidual sets whose largest element e has gcd(e,6) = 1. Compare
the largest flank with the multiple(s) of 6 in the set as flanks: failures and minimum number of
good openings. Exact integers."""
import sys, math, importlib.util
from itertools import combinations
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1])
def G(S, b): return sum(1 for k in range(b) if all(b <= (a*(6*k+1)) % (6*b) <= 5*b for a in S))
n = 0; fl = Counter(); minG = {"largest": (10**9, None), "mult6": (10**9, None), "either": (10**9, None)}
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    e = S[-1]
    if math.gcd(e, 6) != 1: continue
    n += 1
    gl = G(S, e); gm = max(G(S, b) for b in S if b % 6 == 0)
    for name, v in (("largest", gl), ("mult6", gm), ("either", max(gl, gm))):
        if v == 0: fl[name] += 1
        elif v < minG[name][0]: minG[name] = (v, S)
print(f"HI={HI}: coprime-largest residual sets={n}")
for name in ("largest", "mult6", "either"):
    print(f"  {name:8s}: failures={fl[name]}, min good openings={minG[name][0]} at {minG[name][1]}")
