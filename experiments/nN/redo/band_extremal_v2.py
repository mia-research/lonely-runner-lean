"""E121: the band's supremum of R*, pushed hard.  Multi-start local search at fine scale (d1 = 27720), seeded from
v1's late shapes and random AP deviations; moves of every size; exact cascade.  Reports the best shapes."""
import random, sys
from fractions import Fraction as F
from math import floor
from multiprocessing import Pool
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return 8 * T[0] * t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
D1 = 27720
SEEDS = [(1, 2.3091, 3.1726, 4.1869, 5.2226, 5.7861, 7.4385), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302),
         (1, 3.15, 4.2099, 4.7242, 5.225, 5.7897, 7.4429)]
def climb(seed):
    rnd = random.Random(seed)
    if seed < 24: base = SEEDS[seed % 3]
    else: base = [1] + sorted(j + rnd.uniform(-0.5, 0.5) for j in range(2, 7)) + [rnd.uniform(7.01, 8.99)]
    T = tuple(sorted(set(int(round(x * D1)) for x in base)))
    if len(T) < 7 or not (7 * T[0] < T[-1] < 9 * T[0]): return (0, None)
    R = cascade(T); best = (R, T); temp = 0
    for step in range(6000):
        L = list(T); i = rnd.randrange(1, 7); sc = rnd.choice((1, 5, 30, 150, 800))
        L[i] += rnd.randrange(-sc, sc + 1)
        U = tuple(sorted(set(L)))
        if len(U) < 7 or U[0] != D1 or not (7 * U[0] < U[-1] < 9 * U[0]): continue
        R2 = cascade(U)
        if R2 >= R or rnd.random() < 0.02: T, R = U, R2
        if R > best[0]: best = (R, T)
    return best
if __name__ == '__main__':
    with Pool(8) as p: res = p.map(climb, range(64))
    res = sorted([r for r in res if r[1]], reverse=True)
    print("best R* over 64 climbs:")
    for R, T in res[:8]:
        print("  R* = %.5f  shape %s" % (float(R), ["%.4f" % (d / D1) for d in T]))
    print("any R* > 15:", any(r[0] > 15 for r in res))
