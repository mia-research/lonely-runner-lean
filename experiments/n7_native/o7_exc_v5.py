#!/usr/bin/env python3
"""Order seven: share of sets containing a k-term arithmetic progression (k = 4, 5), by class, primitive <= H.
Motivated by o7_exc_v4: the T6 sets carry runs such as (4,5,6,7), (6,7,8,9), (2,4,6,8,10), (3,6,9,12,15)."""
import math, sys
from itertools import combinations
from collections import Counter
exec(open("o7_map_v1.py").read().split("def run(")[0])
H = int(sys.argv[1]) if len(sys.argv) > 1 else 30
def longest_ap(S):
    s = set(S); best = 2
    for a, b in combinations(S, 2):
        d = b - a; n = 2
        while b + (n - 1) * d in s: n += 1
        best = max(best, n)
    return best
tab = Counter(); tot = Counter()
for S in combinations(range(1, H + 1), 6):
    if math.gcd(*S) != 1: continue
    k, _ = classify(S); a = min(longest_ap(S), 5)
    tab[(k, a)] += 1; tot[k] += 1
print(f"primitive <= {H}: longest arithmetic progression (capped at 5) by class")
for k in ("T4", "T5", "T6", "TIGHT"):
    print(f"   {k} ({tot[k]}):", {a: f"{tab[(k, a)]} ({tab[(k, a)] / tot[k]:.2%})" for a in (2, 3, 4, 5)})
