"""Which runner e and which lap K the cascade's isolation t* = (8K+1)/(8e) sits on, read against the arrangement.
Every set of 7 distinct whole-number readings in 1..24 (the slowest runner, every runner moving); only sets not
isolated at the bound (K = 0, e = d_min).  For each: the rank of e among the readings, K, the displacement
R* = 8 d_min t*, whether e was in the slot at the bound (a collider there, i.e. e mod 8 d_min within d_min of 0), and
the ratio e / ((8K+1) d_min) (1 means e sits exactly one opening past a multiple of 8 d_min).  Exact."""
import itertools
from fractions import Fraction as F
from math import floor
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
    for e in T:
        x = e * t - E8
        if x.denominator == 1: return e, int(x)

def chunk(first):
    c = Counter(); rank = Counter(); lap = Counter(); rbin = Counter(); ratio = Counter(); coll = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest; m = T[0]; ts = cascade(T)
        e, K = landing(T, ts)
        if K == 0 and e == m: c['bound'] += 1; continue
        c['displaced'] += 1
        rank[T.index(e) + 1] += 1; lap[K] += 1
        R = 8 * m * ts; rbin[floor(R * 2) / 2] += 1
        colliders = [d for d in T if nd(F(d, 8 * m)) < E8]
        coll['setter was a collider at the bound' if e in colliders else 'setter was clear at the bound'] += 1
        r = F(e, (8 * K + 1) * m)
        ratio['e < (8K+1) d_min' if r < 1 else ('= ' if r == 1 else 'e > (8K+1) d_min')] += 1
    return c, rank, lap, rbin, ratio, coll

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    acc = [Counter() for _ in range(6)]
    for p in parts:
        for a, b in zip(acc, p): a.update(b)
    names = ['sets', 'rank of setter e (1 = d_min, 7 = largest)', 'lap K', 'R* = 8 d_min t*, in halves',
             'e against (8K+1) d_min', 'setter at the bound']
    for n, a in zip(names, acc): print(f"{n}: {sorted(a.items(), key=lambda x: str(x[0]))}")
