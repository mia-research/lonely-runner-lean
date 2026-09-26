"""The nudge generalised to every ladder rung.  For the reading sets settled by none of the proved lemmas
(lemma_map_v1), test the family: t0 = a/q (q = 2..8, 1 <= a < q, gcd(a, q) = 1), then for each reading p the instants
nearest t0 at which p sits exactly on a slot edge, t = (M +- 1/8)/p with M within 1 of p*t0; the set is settled by the
family if some such t is lonely.  Exact.  Also the smallest q that works, and whether the pusher is the largest reading."""
import itertools
from fractions import Fraction as F
from math import gcd, floor
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd
from lemma_map_v1 import TESTS

def lonely(T, t): return t > 0 and all(nd(d * t) >= F(1, 8) for d in T)

def ladder_nudge(T):
    for q in range(2, 9):
        for a in range(1, q):
            if gcd(a, q) != 1: continue
            t0 = F(a, q)
            for p in T:
                M0 = floor(p * t0)
                for M in (M0 - 1, M0, M0 + 1, M0 + 2):
                    for s in (F(1, 8), F(-1, 8)):
                        t = (M + s) / p
                        if abs(t - t0) <= F(1, 8) / min(T) and lonely(T, t):
                            return q, p == T[-1], t
    return None

def chunk(first):
    c = Counter(); miss = []; n = 0
    for rest in itertools.combinations(range(first + 1, 33), 6):
        T = (first,) + rest
        if any(f(T) for _, f in TESTS): continue
        n += 1
        r = ladder_nudge(T)
        if r is None:
            c['not settled'] += 1
            if len(miss) < 20: miss.append(T)
        else: c[('q', r[0], 'pusher is the largest' if r[1] else 'pusher not the largest')] += 1
    return n, c, miss

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 27))
    n = 0; c = Counter(); miss = []
    for a, b, m in parts: n += a; c.update(b); miss += m
    print(f"sets settled by none of the proved lemmas: {n}")
    for k, v in sorted(c.items(), key=lambda x: -x[1]): print(f"  {k}: {v}")
    print(f"  examples still unsettled: {miss[:15]}")
