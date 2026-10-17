#!/usr/bin/env python3
"""7-adic grid levels at high valuations (EXACT): random primitive six-sets with planted multiples of 7^b (b = 1..4,
one to three runners), speeds up to 10^6; the lowest grid level a in nu_max+1 .. nu_max+3 with a lonely k/7^a.
Tabulates (nu_max, a - nu_max) and lists failures."""
import sys, math, random
from collections import Counter
def v7(x):
    k = 0
    while x % 7 == 0: x //= 7; k += 1
    return k
def grid(S, a):
    M = 7 ** a; lo, hi = 7 ** (a - 1), 6 * 7 ** (a - 1)
    R = [d % M for d in S]
    for k in range(1, M):
        if k % 7 and all(lo <= (r * k) % M <= hi for r in R): return True
    return False
rnd = random.Random(5); c = Counter(); fails = []
for _ in range(int(sys.argv[1])):
    b = rnd.randint(1, 4); nm = rnd.randint(1, 3)
    planted = [7 ** b * rnd.choice([x for x in range(1, 2000) if x % 7]) for _ in range(nm)]
    others = []
    while len(others) < 6 - nm:
        x = rnd.randint(1, 10**6)
        others.append(x)
    S = tuple(sorted(set(planted + others)))
    if len(S) < 6 or math.gcd(*S) != 1: continue
    m = max(v7(d) for d in S)
    lvl = next((a for a in range(m + 1, m + 4) if grid(S, a)), None)
    c[(m, None if lvl is None else lvl - m)] += 1
    if lvl is None: fails.append(S)
print("(nu_max, level - nu_max):", sorted(c.items(), key=str))
print("failures:", fails[:10], len(fails))
