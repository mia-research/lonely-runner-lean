#!/usr/bin/env python3
"""Non-divisible case: primitive SixResidual sets whose largest element e is NOT the unique
multiple of 6. Splits by g = gcd(e, 6) (the order of the coarse shift group: openings
j = u*(e/g) + i shift each d by (e/g)*(d*u mod g)), and by number of multiples of 6.
Reports counts, largest-flank failures, and the minimum number of good openings G per group.
Exact integers."""
import sys, math, importlib.util
from itertools import combinations
from collections import Counter, defaultdict
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1])
cnt = Counter(); fail = Counter(); minG = defaultdict(lambda: (10**9, None))
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    e = S[-1]; M = sum(d % 6 == 0 for d in S)
    if e % 6 == 0 and M == 1: continue
    g = math.gcd(e, 6); key = (g, M)
    cnt[key] += 1
    G = sum(1 for j in range(e) if all(e <= (d * (6*j+1)) % (6*e) <= 5*e for d in S))
    if G == 0: fail[key] += 1
    elif G < minG[key][0]: minG[key] = (G, S)
print(f"HI={HI}: non-divisible residual sets={sum(cnt.values())}")
for key in sorted(cnt):
    g, M = key
    print(f"  gcd(e,6)={g}, multiples of 6={M}: sets={cnt[key]}, largest-flank failures={fail[key]}, min good openings={minG[key][0]} at {minG[key][1]}")
