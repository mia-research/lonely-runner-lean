"""E117: whole-number slot sets through the cascade.  Exact.

Population: 7-sets T of distinct readings in 1..N (the slowest runner of c, c+d1, ...), with
  a reading = 0 mod 8 (a runner in the subject's slot at t = 1/8: R6 at q = 8 fails),
  cost = sum over non-multiples of 8 of max(2, gcd(d, 8)) >= 8 (descent fails),
  max > 7 min (R1 fails).
Recorded: the cascade landing t* = (8K+1)/(8e); whether the flank e is a collider (8 | e);
the flank's residue mod 8; K; R* = 8 d_min t*; and the colliders' own state at t*.
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

def landing(T, t):
    out = []
    for e in T:
        x = e * t - E8
        if x.denominator == 1: out.append((e, int(x)))
    return out

N = int(sys.argv[1]) if len(sys.argv) > 1 else 24

def chunk(first):
    c = Counter(); ex = {}
    for rest in itertools.combinations(range(first + 1, N + 1), 6):
        T = (first,) + rest
        C = [d for d in T if d % 8 == 0]
        if not C: continue
        cost = sum(max(2, gcd(d, 8)) for d in T if d % 8)
        if cost < 8: continue
        if T[-1] <= 7 * T[0]: continue
        t = cascade(T)
        L = landing(T, t)
        e, K = min(L)            # smallest flank at the landing (ties are rare)
        col = e % 8 == 0
        R = 8 * T[0] * t
        key = ('collider-flank' if col else 'noncollider-flank r=%d' % (e % 8), 'K=%d' % K if K < 4 else 'K>=4',
               'R<=1' if R <= 1 else ('R<2' if R < 2 else 'R>=2'), 'nC=%d' % len(C))
        c[key] += 1
        ex.setdefault(key, (T, e, K, str(t)))
    return c, ex

if __name__ == '__main__':
    tot = Counter(); exs = {}
    with Pool(8) as p:
        for c, ex in p.imap_unordered(chunk, range(1, N - 5)):
            tot.update(c)
            for k, v in ex.items(): exs.setdefault(k, v)
    print("N =", N, " slot sets (8 | some d, cost >= 8, max > 7 min):", sum(tot.values()))
    for k, v in sorted(tot.items(), key=lambda kv: -kv[1]):
        print("  %7d  %-26s %-6s %-5s %-5s  e.g. %s flank %d lap %d t* %s" % ((v,) + k + exs[k]))
