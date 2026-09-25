"""R by the grid lemma (pigeonhole), and what it leaves.

At t = a/q (a a unit mod q) the offsets e_i a/q sit on the grid (1/q)Z.  Pigeonhole: q = 7 and at
most six offsets leaves an empty slot, so a gap >= 2/7 > 1/4; q in {2,3}: gap >= 1/3; q = 6 with at
most five offsets: gap >= 1/3.  A core runner c is clear with room at a/q iff q does not divide c.
So R holds unless (f = 6) 42 | c, or (f = 5) some core runner is divisible by 6 and some by 7.

Part 1: check the grid criterion against the exhaustive R data (sync_block_v2's range, [1,16]): every
case the criterion claims is correct, exactly.
Part 2: the divisible cores left over, sampled with large offsets: the least q (any q <= 60, any unit
a) at which the core is strictly clear at a/q and the offsets leave a gap > 1/4.  Exact.
"""
import random
from fractions import Fraction as Fr
from itertools import combinations
from math import gcd
def nd(x): x = x % 1; return min(x, 1 - x)
def max_gap(pts):
    p = sorted(set(x % 1 for x in pts)); g = [p[i + 1] - p[i] for i in range(len(p) - 1)] + [1 - p[-1] + p[0]]
    return max(g)
def works(C, e, q, a):
    t = Fr(a, q)
    return all(nd(c * t) > Fr(1, 8) for c in C) and max_gap([x * t for x in e]) > Fr(1, 4)
def grid_q(C, e):
    f = len(e)
    for q in ((2, 3, 6, 7) if f == 5 else (2, 3, 7)):
        for a in range(1, q):
            if gcd(a, q) == 1 and works(C, e, q, a): return q
    return None
wrong = claimed = total = 0
for f, c in ((5, 2), (6, 1)):
    for C in combinations(range(1, 17), c):
        for off in combinations(range(1, 17), f - 1):
            total += 1; e = (0,) + off
            q = grid_q(C, e)
            if q is not None:
                claimed += 1
                if not works(C, e, q, 1 if q == 2 else next(a for a in range(1, q) if gcd(a, q) == 1 and works(C, e, q, a))): wrong += 1
print(f"Part 1, [1,16]: {total} cases; the grid criterion (q in {{2,3,6,7}} / {{2,3,7}}) settles {claimed}; errors {wrong}")
rnd = random.Random(47)
from collections import Counter
for label, gen in (("f=6, core c = 42k", lambda: ((42 * rnd.randrange(1, 50),), 6)),
                   ("f=5, core {6k, 7m}", lambda: ((6 * rnd.randrange(1, 50), 7 * rnd.randrange(1, 50)), 5))):
    qs = Counter(); none = 0
    for _ in range(2000):
        C, f = gen(); e = (0,) + tuple(sorted(rnd.sample(range(1, 10**6), f - 1)))
        best = next((q for q in range(2, 61) for a in range(1, q) if gcd(a, q) == 1 and works(C, e, q, a)), None)
        if best is None: none += 1
        else: qs[best] += 1
    print(f"Part 2, {label}, offsets up to 10^6: least working q {sorted(qs.items())};  none with q <= 60: {none}")
