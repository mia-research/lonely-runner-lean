"""E120: does the cascade ever leave the slowest runner's first block (R* > 7) in the band 7 d1 < d7 < 9 d1?
Random whole-number sets with d1 up to 400 (so fine shapes), plus an adversarial hill-climb on R*.  Exact."""
import random
from fractions import Fraction as F
from math import floor
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade_R(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return 8 * T[0] * t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
rnd = random.Random(120); best = (0, None); over7 = 0; n = 0
def rand_set(d1):
    top = rnd.randrange(7 * d1 + 1, 9 * d1)
    mid = rnd.sample(range(d1 + 1, top), 5)
    return tuple(sorted([d1, top] + mid))
for trial in range(20000):
    T = rand_set(rnd.randrange(5, 400)); R = cascade_R(T); n += 1
    over7 += R > 7
    if R > best[0]: best = (R, T)
print("random band sets:", n, " R* > 7:", over7, " max R* = %.4f at %s" % (float(best[0]), best[1]))
# hill-climb R* upward
for restart in range(60):
    d1 = rnd.randrange(20, 400); T = rand_set(d1); R = cascade_R(T)
    for step in range(600):
        L = list(T); i = rnd.randrange(1, 7)
        L[i] = max(d1 + 1, min(9 * d1 - 1, L[i] + rnd.choice((-3, -2, -1, 1, 2, 3))))
        U = tuple(sorted(set(L)))
        if len(U) < 7 or not (7 * U[0] < U[-1] < 9 * U[0]): continue
        R2 = cascade_R(U)
        if R2 >= R: T, R = U, R2
    if R > best[0]: best = (R, T)
print("after hill-climb: max R* = %.4f (%s) at %s, spread %.3f" % (float(best[0]), best[0], best[1], best[1][-1] / best[1][0]))
