"""E146: the owner's "d_max or d_min finds the location point".  Case B to readings <= 24: classify each landing as
  d_min: at the bound (lap 0, R = 1: the nearest runner's scale, every other reading taken mod 8 d_min);
  d_max: the flank is the bottom of the fastest lap-1 cluster (cut at 9/7);
  middle: otherwise; for these record the flank's lap-1 cluster, whether the fastest cluster's bottom exit on the same
  lap is blocked, and by whom (rank).  Exact."""
import itertools
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
def study(first):
    C = Counter(); ex = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1]): continue
        cl = [0]
        for i in range(1, 7): cl.append(cl[-1] + (1 if 7 * T[i] >= 9 * T[i - 1] else 0))
        top_bottom = cl.index(cl[-1])
        t = cascade(T); f = next(i for i, d in enumerate(T) if (8 * d * t) % 8 == 1); k = floor(T[f] * t)
        band = 'band' if T[-1] <= 9 * T[0] else 'B>9'
        if k == 0: C[(band, 'd_min: at the bound')] += 1
        elif f == top_bottom: C[(band, 'd_max: bottom of the fastest cluster, lap %s' % (k if k <= 3 else '>=4'))] += 1
        else:
            C[(band, 'middle')] += 1
            if len(ex) < 6: ex.append((T, f, k, cl))
    return C, ex
if __name__ == '__main__':
    C = Counter(); EX = []
    with Pool(8) as p:
        for c, e in p.imap_unordered(study, range(1, 19)): C.update(c); EX += e
    for k, v in sorted(C.items()): print("  %7d  %s" % (v, k))
    for e in EX[:12]: print("   middle:", e)
