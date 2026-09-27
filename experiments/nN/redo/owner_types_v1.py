"""E145: the owner's types (confirmed 2026-09-27): same cluster structure (clusters = maximal runs of consecutive ratio
below rho_k, k the landing lap, k = 0 read as rho_1), the same landing cluster (the one whose bottom is the flank), and
each outlier (runner outside the landing cluster) in the same eighth-slot at the landing instant.  Laps and deviations
inside a slot are not part of the type.  Count distinct types as the readings' range grows; also the number of new types
each step adds.  Exact."""
import itertools, sys
from fractions import Fraction as F
from math import floor
from collections import defaultdict, Counter
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
def otype(T):
    t = cascade(T)
    f = next(i for i, d in enumerate(T) if (8 * d * t) % 8 == 1)
    k = max(floor(T[f] * t), 1); rho = F(8 * k + 1, 8 * k - 1)
    cl = [0]
    for i in range(1, 7): cl.append(cl[-1] + (1 if F(T[i], T[i - 1]) >= rho else 0))
    comp = tuple(Counter(cl)[c] for c in range(cl[-1] + 1))
    lc = cl[f]
    slots = tuple(floor((8 * d * t) % 8) if cl[i] != lc else '-' for i, d in enumerate(T))
    return (comp, lc, slots)
def spread_class(T):
    S = F(T[-1], T[0]); return 'A' if S <= 7 else 'band' if S <= 9 else 'B'
def chunk(args):
    N, first = args; out = defaultdict(set)
    for rest in itertools.combinations(range(first + 1, N + 1), 6):
        T = (first,) + rest
        if F(T[-1], T[0]) > 24: continue
        out[spread_class(T)].add(otype(T))
    return out
if __name__ == '__main__':
    Ns = [int(x) for x in sys.argv[1:]] or [12, 16, 20, 24]
    prev = defaultdict(set)
    with Pool(8) as p:
        for N in Ns:
            cur = defaultdict(set)
            for out in p.imap_unordered(chunk, [(N, a) for a in range(1, N - 5)]):
                for k, v in out.items(): cur[k] |= v
            allc = set().union(*cur.values())
            print("N = %2d: types A %d, band %d, B %d; all %d (new since previous N: %d)" % (
                N, len(cur['A']), len(cur['band']), len(cur['B']), len(allc), len(allc - set().union(*prev.values())) if prev else len(allc)))
            print("   cluster compositions seen:", len({t[0] for t in allc}), "; landing-cluster choices:", len({(t[0], t[1]) for t in allc}))
            sys.stdout.flush(); prev = cur
