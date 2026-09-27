"""E128: coverage of the band and Case B by grid references s_j/m, m <= 2, with classes (relocated, pairwise exact).
Exhaustive over integer sets (readings <= N), parallel.  Reports the least m and any set left."""
import itertools, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from grid_class_v2 import grid_class
N = int(sys.argv[1]); SMAX = int(sys.argv[2])
def chunk(first):
    c = Counter(); left = []
    for rest in itertools.combinations(range(first + 1, N + 1), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1] <= SMAX * T[0]): continue
        m = grid_class([F(d, T[0]) for d in T], M=2)
        c[m] += 1
        if m is None and len(left) < 5: left.append(T)
    return c, left
if __name__ == '__main__':
    tot = Counter(); L = []
    with Pool(10) as p:
        for c, left in p.imap_unordered(chunk, range(1, N - 5)): tot.update(c); L += left
    print("readings <= %d, spread in (7, %d]: least m:" % (N, SMAX), sorted(tot.items(), key=lambda kv: (kv[0] is None, kv[0] or 0)))
    print("  not covered with m <= 2, e.g.", L[:10])
