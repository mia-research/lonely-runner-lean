"""E119: the B1 remainder through the cascade, read on the grid's laps.  Exact.
B1: 7 d1 < d7 < 9 d1; remainder: no reading e carries a two-block instant 9/(8e).  Per set: each cascade move as
R = 8 d1 t, and at the landing each reading's lap block k = floor(position/8) (position = d R / d1, in [8k+1, 8k+7]),
listed from slowest to fastest; the flank's lap K."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def two_block(T):
    return any(all((e <= 9 * d <= 7 * e) or (e <= d and 9 * d <= 15 * e) for d in T) for e in T)
def cascade(T):
    t = F(1, 8 * T[0]); path = []
    while True:
        way = [d for d in T if nd(d * t) < E8]
        path.append((8 * T[0] * t, tuple(way)))
        if not way: return t, path
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
N = 40; pat = Counter(); ex = {}
for T in itertools.combinations(range(1, N + 1), 7):
    if not (7 * T[0] < T[-1] < 9 * T[0]) or two_block(T): continue
    t, path = cascade(T)
    blocks = tuple(floor(d * t * 8 / 8) for d in T)     # lap of each reading at t*: floor(d t)
    K = next(int(e * t - E8) for e in T if (e * t - E8).denominator == 1)
    key = ('laps ' + ''.join(map(str, blocks)), 'flank lap %d' % K, 'moves %d' % (len(path) - 1))
    pat[key] += 1; ex.setdefault(key, (T, [(str(R), w) for R, w in path]))
print("B1 remainder sets, readings <=", N, ":", sum(pat.values()))
for k, v in pat.most_common(25): print("  %6d  %s  e.g. %s" % (v, k, ex[k][0]))
k0 = pat.most_common(1)[0][0]; print("\ncascade path of", ex[k0][0], ":", ex[k0][1])
