"""E128: the Case B sets (readings <= 24) not covered by grid references s_j/m with m <= 2: least m up to 12, and the
cascade's landing R* for each."""
import itertools, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
from grid_class_v2 import grid_class
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
def job(T):
    s = [F(d, T[0]) for d in T]
    if grid_class(s, M=2) is not None: return None
    return (T, grid_class(s, M=12), cascade(T))
if __name__ == '__main__':
    sets = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1] <= 24 * T[0]]
    with Pool(10) as p: res = [r for r in p.map(job, sets, chunksize=200) if r]
    print("exceptions (m <= 2 fails):", len(res))
    print("  least m up to 12:", sorted(Counter(r[1] for r in res).items(), key=lambda kv: (kv[0] is None, kv[0] or 0)))
    print("  spread of the exceptions:", sorted(Counter(round(r[0][-1] / r[0][0]) for r in res).items()))
    print("  cascade R* range: %.3f .. %.3f" % (min(float(r[2]) for r in res), max(float(r[2]) for r in res)))
    for T, m, R in res[:12]: print("   ", T, "least m", m, "R* = %s (%.3f)" % (R, float(R)))
