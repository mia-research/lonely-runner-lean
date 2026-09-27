"""E117: the collision band.  Every 7-set of readings in 1..N with 7 d_min < d_max < 9 d_min (the fastest runner
lapped once into the subject's slot at the AP scale d_min).  Exact.
Per set: is the bound 1/(8 d_min) clear; else the least lap K >= 1 such that some reading e has its opening
(8K+1)/(8e) clear; and where the cascade lands."""
import itertools, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def lonely(T, t): return all(nd(d * t) >= E8 for d in T)
def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 32
def chunk(first):
    c = Counter(); ex = []
    for rest in itertools.combinations(range(first + 1, min(N, 9 * first - 1) + 1), 6):
        T = (first,) + rest
        if not (7 * first < T[-1] < 9 * first): continue
        if lonely(T, F(1, 8 * first)): c['bound clear'] += 1; continue
        K = next(K for K in itertools.count(1) if any(lonely(T, F(8 * K + 1, 8 * e)) for e in T))
        es = [e for e in T if lonely(T, F(8 * K + 1, 8 * e))]
        t = cascade(T); Kc = next(int(e * t - E8) for e in T if (e * t - E8).denominator == 1)
        c[('least K with a clear opening = %d' % K, 'cascade lap %d' % Kc)] += 1
        if K >= 2 and len(ex) < 4: ex.append((T, K, es))
    return c, ex
if __name__ == '__main__':
    tot = Counter(); exs = []
    with Pool(8) as p:
        for c, ex in p.imap_unordered(chunk, range(1, N // 7 + 1)): tot.update(c); exs += ex
    print("N =", N, "collision-band sets:", sum(tot.values()))
    for k, v in sorted(tot.items(), key=str): print("  %8d  %s" % (v, k))
    print("  K >= 2 examples:", exs[:8])
