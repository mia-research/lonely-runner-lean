"""E117: slot sets on the lattice ladder, through the cascade.  Exact.

L0 = least live lattice (no reading = 0 mod 8 L0).  L0 >= 2 exactly when a reading is = 0 mod 8 (a slot set).
Per set: L0; whether L0 clears; the sequence of live lattices up to the least clearing one D*;
and the cascade landing (e, K): is its instant a lattice instant of D*? of 2*L0?  is e a multiple of L0?
"""
import itertools, sys
from fractions import Fraction as F
from math import gcd, floor
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
def live(T, D): return all(d % (8 * D) for d in T)
def clears(T, D): return [j for j in range(D) if all(D <= (d * (8 * j + 1)) % (8 * D) <= 7 * D for d in T)]

N = int(sys.argv[1]) if len(sys.argv) > 1 else 24
def chunk(first):
    c = Counter()
    for rest in itertools.combinations(range(first + 1, N + 1), 6):
        T = (first,) + rest
        L0 = next(D for D in itertools.count(1) if live(T, D))
        if L0 == 1: c[('L0=1', 'clears')] += 1; continue
        seq = []; D = L0
        while True:
            if live(T, D):
                if clears(T, D): break
                seq.append(D)
            D += 1
        Ds = D
        t = cascade(T)
        tag = 'L0 clears' if not seq else 'L0 fails; D*-L0=%d' % (Ds - L0) if Ds - L0 < 6 else 'L0 fails; D*-L0>=6'
        onDs = (t * 8 * Ds - 1) % 8 == 0 and (t * 8 * Ds).denominator == 1
        c[('L0=%d' % L0, tag, 'cascade on D*' if onDs else 'cascade elsewhere')] += 1
    return c
if __name__ == '__main__':
    tot = Counter()
    with Pool(8) as p:
        for c in p.imap_unordered(chunk, range(1, N - 5)): tot.update(c)
    print("N =", N, "sets:", sum(tot.values()))
    for k, v in sorted(tot.items()): print("  %7d  %s" % (v, "  ".join(k)))
