#!/usr/bin/env python3
"""Level-3 rescue of the 48 failing level-2 orbits (EXACT, complete).  For a failing orbit (u1..u5 mod 49) and the
single multiple m = 7 m' (7 not dividing m'), level 3 needs a unit k mod 343 with every unit lift u mod 343 satisfying
u k mod 343 in [49, 294], and m' k mod 49 in [7, 42].  All 7^5 unit lifts and all 42 classes of m' mod 49 are checked
(bitmasks over the 294 units k).  Reports orbits/lift tuples with no level-3 instant."""
from itertools import product
import ast
K = [k for k in range(1, 343) if k % 7]
idx = {k: i for i, k in enumerate(K)}
def mask(pred):
    m = 0
    for i, k in enumerate(K):
        if pred(k): m |= 1 << i
    return m
umask = {r: mask(lambda k, r=r: 49 <= (r * k) % 343 <= 294) for r in range(343) if r % 7}
mmask = {c: mask(lambda k, c=c: 7 <= (c * k) % 49 <= 42) for c in range(49) if c % 7}
orbits = [ast.literal_eval(l) for l in open("seven_mod49_fail_r5.txt") if l.strip()]
bad = 0; worst = []
for orb in orbits:
    lifts = [[u + 49 * x for x in range(7)] for u in orb]
    nb = 0
    for tup in product(*lifts):
        a = umask[tup[0]] & umask[tup[1]] & umask[tup[2]] & umask[tup[3]] & umask[tup[4]]
        for c, mm in mmask.items():
            if not (a & mm): nb += 1
    if nb: bad += 1; worst.append((orb, nb))
print(f"{len(orbits)} failing level-2 orbits; orbits with some lift (units mod 343, m' mod 49) having no level-3 instant: {bad}")
print("   (orbit, number of failing (lift, m') pairs):", worst[:20])
