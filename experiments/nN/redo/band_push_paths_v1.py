"""E121: how many distinct cascade push sequences does the band have?  A push = (rank of the blocker, lap it is pushed
to); a move = the set of pushes; a path = the sequence of moves until the landing.  Exhaustive to N; plus random fine
shapes to see whether new paths keep appearing.  Exact."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def path(T):
    t = F(1, 8 * T[0]); P = []
    while True:
        way = [(i, floor(d * t - E8) + 1) for i, d in enumerate(T) if nd(d * t) < E8]
        if not way: return tuple(P)
        P.append(tuple(way))
        t = max((F(8 * k + 1, 8 * T[i])) for i, k in way)
seen = Counter(); growth = []
for N in (24, 32, 40):
    for T in itertools.combinations(range(1, N + 1), 7):
        if 7 * T[0] < T[-1] < 9 * T[0]: seen[path(T)] += 1
    growth.append((N, len(seen)))
print("distinct push paths, exhaustive:", growth)
rnd = random.Random(3); new = 0
for trial in range(20000):
    d1 = rnd.randrange(40, 3000); top = rnd.randrange(7 * d1 + 1, 9 * d1)
    T = tuple(sorted([d1, top] + rnd.sample(range(d1 + 1, top), 5)))
    p = path(T)
    if p not in seen: new += 1; seen[p] += 1
print("random fine shapes 20,000: paths not seen before:", new)
lens = Counter(len(p) for p in seen); print("path lengths:", sorted(lens.items()))
