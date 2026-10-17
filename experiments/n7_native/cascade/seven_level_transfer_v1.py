#!/usr/bin/env python3
"""Do level-a failures of five units transfer from level 2?  Sample random 5-tuples of units mod 7^a (a = 3, 4), test
P(U, a): some unit k mod 7^a with every u k mod 7^a in [7^(a-1), 6*7^(a-1)].  Tabulate against: U mod 49 in a failing
level-2 orbit (seven_mod49_fail_r5.txt), and U mod 7^(a-1) failing level a-1.  Also exhaustive over the 7^5 lifts of
each of the 48 failing orbits at a = 3 (do lifts of failing orbits fail at level 3?)."""
import sys, random, ast
from itertools import product
from collections import Counter
def P(U, a):
    M = 7 ** a; lo, hi = 7 ** (a - 1), 6 * 7 ** (a - 1)
    return any(all(lo <= (u * k) % M <= hi for u in U) for k in range(1, M) if k % 7)
Ufail = set()
units49 = [u for u in range(1, 49) if u % 7]
for l in open("seven_mod49_fail_r5.txt"):
    if l.strip():
        o = ast.literal_eval(l)
        for c in units49: Ufail.add(tuple(sorted((u * c) % 49 for u in o)))
rnd = random.Random(1); c = Counter()
for a in (3, 4):
    M = 7 ** a
    for _ in range(int(sys.argv[1])):
        U = tuple(sorted(rnd.choice([x for x in range(1, M) if x % 7]) for _ in range(5)))
        f49 = tuple(sorted(u % 49 for u in U)) in Ufail
        fprev = not P(tuple(u % (M // 7) for u in U), a - 1)
        c[(a, P(U, a), f49, fprev)] += 1
print("(level a, P(U,a), U mod 49 failing at level 2, U mod 7^(a-1) failing at level a-1):")
for k, v in sorted(c.items()): print("  ", k, v)
lift_fail = 0; tot = 0
for l in open("seven_mod49_fail_r5.txt"):
    if not l.strip(): continue
    o = ast.literal_eval(l)
    for tup in product(*[[u + 49 * x for x in range(7)] for u in o]):
        tot += 1; lift_fail += not P(tup, 3)
print(f"lifts of the 48 failing orbits to mod 343: {tot}; failing level 3 as units only: {lift_fail}")
