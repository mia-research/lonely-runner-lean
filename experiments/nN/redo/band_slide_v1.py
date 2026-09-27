"""E122: late band shapes (copy 0 fully covered): which runner's slide opens copy 1's gap?  Many late shapes by local
search on fine scale; per shape: landing R* (copy 1), the runner whose window ends at R* (leaves the slot there), the
runner covering R*-8 in copy 0 and how far into its window R*-8 sits.  Exact."""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
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
D1 = 27720
SEEDS = [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.3091, 3.1726, 4.1869, 5.2226, 5.7861, 7.4385),
         (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302), (1, 3.15, 4.2099, 4.7242, 5.225, 5.7897, 7.4429)]
def late(seed):
    rnd = random.Random(seed); out = []
    T = tuple(int(round(x * D1)) for x in SEEDS[seed % 4]); R = 8 * T[0] * cascade(T)
    for step in range(3000):
        L = list(T); i = rnd.randrange(1, 7); L[i] += rnd.randrange(-600, 601)
        U = tuple(sorted(set(L)))
        if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
        R2 = 8 * U[0] * cascade(U)
        if R2 > 7:
            T, R = U, R2
            if step % 20 == 0: out.append(T)
    return out

if __name__ == '__main__':
    with Pool(8) as p: shapes = [T for L in p.map(late, range(48)) for T in L]
    shapes = sorted(set(shapes)); print("late shapes found:", len(shapes))
    c = Counter()
    for T in shapes:
        s = [F(d, D1) for d in T]; t = cascade(T); R = 8 * T[0] * t
        leave = [i for i, x in enumerate(s) if ((x * R - 1) / 8).denominator == 1]   # at 8k+1 exactly
        R0 = R - 8
        cov0 = [i for i, x in enumerate(s) if nd(x * R0 / 8) < E8]                 # blockers of R-8 in copy 0
        c[('flank rank %s' % leave, 'copy-0 blockers at R*-8 %s' % cov0)] += 1
    for k, v in c.most_common(20): print("  %4d  %s" % (v, k))
