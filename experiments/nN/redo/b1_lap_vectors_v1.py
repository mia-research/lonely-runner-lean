"""E120: the lap assignments the cascade lands on in the band 7 d1 < d7 < 9 d1 (and its remainder).  At the landing R*,
reading s_i sits in lap k_i = floor(s_i R*/8).  Loneliness at a lap vector is pairwise (1-D Helly).  Exact."""
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
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
N = 40; allv = Counter(); remv = Counter(); Rmax = 0
for T in itertools.combinations(range(1, N + 1), 7):
    if not (7 * T[0] < T[-1] < 9 * T[0]): continue
    t = cascade(T); v = tuple(int(d * t) for d in T); Rmax = max(Rmax, 8 * T[0] * t)
    allv[v] += 1
    if not two_block(T): remv[v] += 1
print("band sets to", N, ": landing lap vectors", len(allv), "; max R* %.4f" % float(Rmax))
print("remainder sets:", sum(remv.values()), "; landing lap vectors", len(remv))
print("monotone (k_i <= k_{i+1}) in all:", all(all(a <= b for a, b in zip(v, v[1:])) for v in allv))
for v, n in remv.most_common(40): print("   ", ''.join(map(str, v)), n)
