#!/usr/bin/env python3
"""Observation only. Exhaustive: every primitive 5-subset of [1, H] (H = 40, then 60): q* = least q with a lonely
unit instant c/q (all five readings (d c mod q)/q in [1/6, 5/6]). Distribution, maximum, and the sets attaining it."""
import math, sys
from itertools import combinations
from collections import Counter
def blocks(d, c, q): x = (d * c) % q; return 6 * x < q or 6 * x > 5 * q
def qstar(S):
    q = 2
    while True:
        if any(math.gcd(c, q) == 1 and not any(blocks(d, c, q) for d in S) for c in range(1, q)): return q
        q += 1
for H in map(int, sys.argv[1:]):
    dist = Counter(); worst = []
    for S in combinations(range(1, H + 1), 5):
        if math.gcd(*S) != 1: continue
        q = qstar(S); dist[q] += 1
        if not worst or q > worst[0][0]: worst = [(q, S)]
        elif q == worst[0][0] and len(worst) < 12: worst.append((q, S))
    print(f"H={H}: primitive 5-sets {sum(dist.values())}; q* distribution {sorted(dist.items())}")
    print(f"   max q* = {worst[0][0]} at {[s for _, s in worst]}")
