"""E121: how close can the band's cascade come to R = 7?  Local search on fine shapes (d1 = 2520*m scale), started
from the exhaustive extremes to 40, maximising R*.  Exact.  Output: the best shapes and their cascades."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor
from multiprocessing import Pool
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * T[0]); n = 0
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return 8 * T[0] * t, n
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way); n += 1
def seeds():
    out = []
    for T in itertools.combinations(range(1, 41), 7):
        if 7 * T[0] < T[-1] < 9 * T[0]:
            R, n = cascade(T)
            if R > 5.5: out.append((R, T))
    out.sort(reverse=True); return [T for R, T in out[:64]]
SC = 2520
def climb(args):
    T0, seed = args; rnd = random.Random(seed)
    T = tuple(d * SC // T0[0] * T0[0] // T0[0] for d in T0)  # placeholder, replaced below
    T = tuple(sorted(d * (SC // T0[0] if SC % T0[0] == 0 else SC) for d in T0))
    R, n = cascade(T); best = (R, T)
    for step in range(4000):
        L = list(T); i = rnd.randrange(1, 7); scale = rnd.choice((1, 3, 10, 30, 100))
        L[i] += rnd.randrange(-scale, scale + 1)
        U = tuple(sorted(set(L)))
        if len(U) < 7 or U[0] != T[0] or not (7 * U[0] < U[-1] < 9 * U[0]): continue
        R2, n2 = cascade(U)
        if R2 >= R: T, R = U, R2
        if R > best[0]: best = (R, T)
    return best
if __name__ == '__main__':
    S = seeds(); print("seeds:", len(S)); sys.stdout.flush()
    with Pool(8) as p:
        res = p.map(climb, [(T, i) for i, T in enumerate(S)])
    res.sort(reverse=True)
    for R, T in res[:10]:
        u = [float(F(d, T[0])) for d in T]
        print("R* = %.5f  shape/d1 = %s  %s" % (float(R), ["%.4f" % x for x in u], T))
