#!/usr/bin/env python3
"""Provable split-fold (EXACT Fractions). The split lemma with every ingredient replaced by a bound that has an
analytic proof:
 - window of the slow block S = (v1..vj): W_1 = 5/(7 v1); W_j >= 2 (1/(j+1) - 1/7)/v_j for j >= 2 (native order j+1
   gives an instant at distance >= 1/(j+1); each runner of S moves at most v_j per unit time);
 - gap of the fast block F = (u1 < ... < ur), window w = 3/(28 v5):
     G(u_r) = 2/(7 u_r) + 2w   (single runner: band stretches 5/(7u) >= w, gaps 2/(7u));
     G(u1, F') <= 2/(7 u1) + 2 G(F')  provided 5/(7 u1) >= G(F')   (stretch recursion);  else no bound.
 Closes P when W_j >= G(F) for some j.  Reports coverage over primitive prefixes <= H and, for the not-closed ones,
 the largest consecutive ratio and the smallest v1/v5."""
import math, sys
from fractions import Fraction as Fr
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
def Gb(F, w):
    G = Fr(2, 7 * F[-1]) + 2 * w
    for u in reversed(F[:-1]):
        if Fr(5, 7 * u) < G: return None
        G = Fr(2, 7 * u) + 2 * G
    return G
def closes(P):
    w = Fr(3, 28 * P[4])
    for j in range(1, 5):
        W = Fr(5, 7 * P[0]) if j == 1 else 2 * (Fr(1, j + 1) - Fr(1, 7)) / P[j - 1]
        G = Gb(P[j:], w)
        if G is not None and W >= G: return j
    return 0
def work(args):
    v1, H = args; c = Counter(); maxr = Fr(0); minx = None; ex = None
    for rest in combinations(range(v1 + 1, H + 1), 4):
        P = (v1,) + rest
        if math.gcd(*P) != 1: continue
        j = closes(P); c[j] += 1
        if j == 0:
            r = max(Fr(P[i + 1], P[i]) for i in range(4))
            if r > maxr: maxr = r; ex = P
            x = Fr(P[0], P[4])
            if minx is None or x < minx[0]: minx = (x, P)
    return c, (maxr, ex), minx
if __name__ == "__main__":
    H = int(sys.argv[1])
    with Pool(10) as pool: res = pool.map(work, [(v1, H) for v1 in range(1, H - 3)], chunksize=1)
    c = Counter()
    for r in res: c += r[0]
    n = sum(c.values()); mr = max((r[1] for r in res if r[1][1]), default=None); mx = min((r[2] for r in res if r[2]), default=None)
    print(f"exact, provable split-fold, primitive prefixes <= {H}: {n}; closed {n - c[0]} ({(n - c[0]) / n:.2%}); "
          f"by split {dict(sorted(c.items()))}")
    print(f"   not closed: largest consecutive ratio {mr[0]} at {mr[1]}; smallest v1/v5 {mx[0]} at {mx[1]}")
