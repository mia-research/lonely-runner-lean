#!/usr/bin/env python3
"""Slow-region D sets (A, B, C fail; EXACT): sample v6 > 100 v1 with v1 in 1..60, collect D sets, and test the next
7-adic grids: t = k / 7^a (a = 2, 3), k not divisible by 7 -- lonely iff every d k mod 7^a is in [7^(a-1), 6 * 7^(a-1)];
and the scaled cell: openings (7j+1)/(7e) of every flank e (any speed).  Reports which close each D set."""
import sys, math, random
sys.path.insert(0, ".")
from collections import Counter
from seven_core_v1 import closer
def grid(S, a):
    M = 7 ** a; lo, hi = 7 ** (a - 1), 6 * 7 ** (a - 1)
    for k in range(1, M):
        if k % 7 == 0: continue
        if all(lo <= (d * k) % M <= hi for d in S): return k
    return None
def lon(S, e, r):
    m = 7 * e
    return all(e <= (d * r) % m <= 6 * e for d in S)
rnd = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 3); N = int(sys.argv[1])
D = []; tot = 0
while tot < N:
    v1 = rnd.randint(1, 60); v6 = rnd.randint(101 * v1, 300 * v1)
    S = (v1, *sorted(rnd.sample(range(v1 + 1, v6), 4)), v6)
    if math.gcd(*S) != 1: continue
    tot += 1
    if closer(S) == "D": D.append(S)
c = Counter(); v1s = Counter(); fl = Counter(); left = []
for S in D:
    v1s[(S[0] % 7 == 0, S[0] % 49 == 0)] += 1
    g2, g3 = grid(S, 2), grid(S, 3)
    flanks = tuple(i + 1 for i, e in enumerate(S) if any(lon(S, e, 7 * j + 1) or lon(S, e, 7 * j + 6) for j in range(e)))
    c[(g2 is not None, g3 is not None)] += 1; fl[flanks] += 1
    if g2 is None and g3 is None and len(left) < 10: left.append((S, flanks))
print(f"{tot} sets with v6 > 100 v1: D sets {len(D)}")
print("  v1 (divisible by 7, by 49):", dict(v1s))
print("  closed by grid k/49, by grid k/343:", dict(c))
print("  flanks carrying a lonely opening:", fl.most_common(8))
print("  closed by neither grid:", left)
