#!/usr/bin/env python3
"""How much of Z/163 can x dilates of the 41-arc cover, at best?

Scaling all w_i by a unit permutes Z/163, so |union| is scale-invariant; every
non-empty set can be scaled to contain w=1.  Enumerating sets containing 1 is
therefore exhaustive.  Reported: max union, hence U_min(x) = 163 - max union,
the fewest mod-163 classes that x speeds with 8|v must leave uncovered.
"""
from itertools import combinations

p, n = 163, 8
h = (p - 1) // n
A = {s % p for s in range(-h, h + 1)}
W = list(range(1, (p - 1) // 2 + 1))
M = {}
for w in W:
    m = 0
    for r in range(p):
        if (r * w) % p in A:
            m |= 1 << r
    M[w] = m
print(f"p={p} n={n} arc |A|={len(A)}  dilate classes={len(W)}")
print(f"{'x':>2} {'max union':>10} {'U_min':>6} {'witness (w_i, scaled to contain 1)':>40}")
base = M[1]
rest = [w for w in W if w != 1]
for x in range(1, 6):
    best, wit = -1, None
    for c in combinations(rest, x - 1):
        u = base
        for w in c:
            u |= M[w]
        pc = u.bit_count()
        if pc > best:
            best, wit = pc, (1,) + c
    print(f"{x:>2} {best:>10} {p-best:>6} {str(wit):>40}")
