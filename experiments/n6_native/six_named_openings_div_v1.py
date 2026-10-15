#!/usr/bin/env python3
"""Divisible case (largest e = 6E, unique multiple of 6). A good opening j (multiplier m = 6j+1) is
NAMED by (x, c) when x*m mod e is c or e-c, with x an element, a pairwise difference, or a pairwise
sum of S (x mod e nonzero), and c >= 1. Reports per set the least c for which some good opening is
named, by family. Exact integers."""
import sys, math, importlib.util
from itertools import combinations
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1]); K = int(sys.argv[2])
dist = Counter(); fam = Counter(); n = 0; worst = []
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    e = S[-1]
    if not (e % 6 == 0 and sum(d % 6 == 0 for d in S) == 1): continue
    n += 1
    good = [6 * j + 1 for j in range(e) if all(e <= (d * (6*j+1)) % (6*e) <= 5*e for d in S)]
    if not good: dist["no good opening"] += 1; continue
    xs = [("ELEM", d) for d in S[:-1]] + [("DIFF", b - a) for a, b in combinations(S, 2)] + \
         [("SUM", a + b) for a, b in combinations(S[:-1], 2)]
    xs = [(f, x % e) for f, x in xs if x % e]
    best = None
    for c in range(1, K + 1):
        for f, x in xs:
            if any((x * m) % e in (c, e - c) for m in good): best = (c, f); break
        if best: break
    if best: dist[best[0]] += 1; fam[best[1]] += 1
    else:
        dist[f">{K}"] += 1
        if len(worst) < 8: worst.append(S)
print(f"HI={HI}, K={K}: divisible-case sets={n}")
print("  least c naming a good opening:", dict(sorted(dist.items(), key=lambda kv: str(kv[0]))))
print("  family:", dict(fam))
print("  examples beyond K:", worst)
