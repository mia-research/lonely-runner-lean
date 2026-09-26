"""Every cascade landing t* = (8K+1)/(8e) is K/e + 1/(8e): the rung a/q = K/e (lowest terms, q = e/gcd(K, e)) plus the
deviation 1/(8e).  At a/q every reading divisible by q sits on a whole lap, so loneliness at t* forces e to be the
least reading divisible by q and every multiple of q to lie in [e, 7e] (rung R1 with multiples' own d_min).  Check this
exactly on every set of 7 distinct whole-number readings in 1..24 (the slowest runner, every runner moving), and record
the rung denominator q the cascade uses, how many readings are multiples of q, and where the non-multiples sit.
Exact."""
import itertools
from fractions import Fraction as F
from math import gcd, floor
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd

E8 = F(1, 8)

def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)

def landing(T, t):
    """The setter e and lap K with e*t = K + 1/8 (the runner exactly at the opening edge)."""
    for e in T:
        x = e * t - E8
        if x.denominator == 1: return e, int(x)
    return None

def chunk(first):
    c = Counter(); qhist = Counter(); mult = Counter(); qbig = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest; ts = cascade(T)
        e, K = landing(T, ts)
        g = gcd(K, e); a, q = K // g, e // g
        M = [d for d in T if d % q == 0]
        c['sets'] += 1
        c['e is least multiple of q'] += (min(M) == e)
        c['multiples in [e,7e]'] += all(e <= w <= 7 * e for w in M)
        qhist[q if q <= 8 else '>8'] += 1
        if q > 8: qbig[q] += 1; mult[len(M)] += 1
    return c, qhist, mult, qbig

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    c = Counter(); qh = Counter(); mu = Counter(); qb = Counter()
    for a, b, m, z in parts: c.update(a); qh.update(b); mu.update(m); qb.update(z)
    for k, v in c.items(): print(f"{k}: {v}")
    print("rung denominator q of the landing:", sorted(qh.items(), key=lambda x: str(x[0]).zfill(3)))
    print("q > 8, by q:", sorted(qb.items()))
    print("q > 8, number of readings divisible by q:", sorted(mu.items()))
