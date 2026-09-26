"""Rung R1: for a ladder rung t0 = a/q (q = 2..8, gcd(a, q) = 1), let D = the readings divisible by q.  At
t = a/q + s/(8 min D), s = +1 or -1, every d in D sits where it sits at D's own bound (d*a/q is a whole number), so D is
clear if it satisfies R1 (max D <= 7 min D); every other reading rides from its nonzero multiple of 1/q.  Test the whole
family (lonely at some such t) exactly on the sets settled by none of the proved lemmas (lemma_map_v1), readings <= 32."""
import itertools
from fractions import Fraction as F
from math import gcd
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd
from lemma_map_v1 import TESTS

def lonely(T, t): return t > 0 and all(nd(d * t) >= F(1, 8) for d in T)

def rung_r1(T):
    for q in range(2, 9):
        D = [d for d in T if d % q == 0]
        if not D: continue
        for a in range(1, q):
            if gcd(a, q) != 1: continue
            for s in (1, -1):
                t = F(a, q) + F(s, 8 * min(D))
                if lonely(T, t): return q
    return None

def chunk(first):
    c = Counter(); miss = []
    for rest in itertools.combinations(range(first + 1, 33), 6):
        T = (first,) + rest
        if any(f(T) for _, f in TESTS): continue
        r = rung_r1(T)
        c[r] += 1
        if r is None and len(miss) < 12: miss.append(T)
    return c, miss

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 27))
    c = Counter(); miss = []
    for a, b in parts: c.update(a); miss += b
    print(f"unsettled sets: {sum(c.values())}")
    print(f"  settled by rung R1, by rung q: {sorted((k, v) for k, v in c.items() if k is not None)}; not settled: {c[None]}")
    print(f"  examples not settled: {miss[:12]}")
