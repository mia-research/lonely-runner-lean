#!/usr/bin/env python3
"""Coprime case, named multiplier families m = c * inv(x) mod e, with x from:
  ELEM: x = d (one element pinned near a sixth-point),
  DIFF: x = d_a - d_b (two elements read alike: a meeting),
  SUM:  x = d_a + d_b (two elements read as mirror images),
for x a unit mod e and 1 <= |c| <= K. Reports, per set, the least |c| using all three families, and
which family achieves the least |c| first. CRT clearance as in v1. Exact integers."""
import sys, math, importlib.util
from itertools import combinations
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1]); K = int(sys.argv[2])
def clear_all(S, e, m):
    einv = 1 if e % 6 == 1 else 5
    for d in S:
        w = (d * m) % e; c = (einv * (d - w)) % 6
        if not (1 <= c <= 4 or (c == 5 and w == 0)): return False
    return True
dist = Counter(); fam = Counter(); n = 0; worst = []
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    e = S[-1]
    if math.gcd(e, 6) != 1: continue
    n += 1
    xs = [("ELEM", d) for d in S[:-1]] + [("DIFF", b - a) for a, b in combinations(S, 2)] + \
         [("SUM", a + b) for a, b in combinations(S[:-1], 2)]
    xs = [(f, x % e) for f, x in xs if x % e and math.gcd(x % e, e) == 1]
    best = None
    for c in range(1, K + 1):
        for f, x in xs:
            for sg in (c, -c):
                if clear_all(S, e, (sg * pow(x, -1, e)) % e): best = (c, f); break
            if best: break
        if best: break
    if best: dist[best[0]] += 1; fam[best[1]] += 1
    else:
        dist[f">{K}"] += 1
        if len(worst) < 8: worst.append(S)
print(f"HI={HI}, K={K}: coprime-case sets={n}")
print("  least |c| over ELEM+DIFF+SUM:", dict(sorted(dist.items(), key=lambda kv: str(kv[0]))))
print("  family achieving it first:", dict(fam))
print("  examples beyond K:", worst)
