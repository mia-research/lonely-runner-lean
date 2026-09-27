"""E123: the 'smaller set' at the landing.  At the cascade's landing R*, the positions p_i = s_i R* mod 8 in [1,7].
Effective places: cluster positions within 1/7 (order seven's slack, in position units 8/7 - 1 = 1/7).  Count clusters.
Also: the least R over all 'merge one close pair' order-7 instants is not computed; this only reads the landing.  Exact."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
def clusters(pos, w=F(1, 7)):
    pos = sorted(pos); n = 1
    for a, b in zip(pos, pos[1:]):
        if b - a > w: n += 1
    return n
c = Counter()
for T in itertools.combinations(range(1, 33), 7):
    if not (7 * T[0] < T[-1] < 9 * T[0]): continue
    t = cascade(T); pos = [(8 * d * t) % 8 for d in T]
    c[clusters(pos)] += 1
print("band sets to 32: effective places at the landing (positions within 1/7 merged):", sorted(c.items()))
