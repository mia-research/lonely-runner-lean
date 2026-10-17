#!/usr/bin/env python3
"""Split-fold lemma, observation (EXACT integers). For a 5-prefix P = (v1..v5) and a split j in 1..4:
 slow block S = (v1..vj), fast block F = (v_{j+1}..v5).  W_j = longest interval with S in band [1/7, 6/7];
 G(F) = least length such that every interval of that length contains a window of length w = 3/(28 v5) with F in band
 (as o7_slow_v1).  If W_j >= G(F), the slow window contains a full G-interval, hence an F-window inside it, with S in
 band throughout: kappa(P) >= 3/28.  (j = 1: W_1 = 5/(7 v1), the slow lemma; j = 4: G(v5) = 1/(2 v5), the fast fold.)
 Reports, over primitive prefixes <= H, the share closed by some split, by split, and the not-closed set: smallest
 v1/v5, and a sample of the not-closed prefixes with the smallest v1/v5."""
import math, sys
from fractions import Fraction as Fr
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
from o7_exact import lcm, inter
def lonely_iv(S, N):
    """lonely intervals of S at [1/7, 6/7], time scaled by N (a multiple of 7 * lcm(S))"""
    cur = None
    for v in S:
        q = N // (7 * v); B = [((7 * m + 1) * q, (7 * m + 6) * q) for m in range(v)]
        cur = B if cur is None else inter(cur, B)
    return cur
def split_ok(P, j):
    S, F = P[:j], P[j:]
    N = 28 * lcm(P)
    W = max((U - L for L, U in lonely_iv(S, N)), default=0)
    iv = lonely_iv(F, N); w = 3 * N // (28 * P[4])
    good = [(L, U) for L, U in iv if U - L >= w]
    if not good: return False
    gaps = [good[(i + 1) % len(good)][0] + (N if i + 1 == len(good) else 0) - good[i][1] for i in range(len(good))]
    return W >= max(gaps) + 2 * w
def work(args):
    v1, H = args; c = Counter(); bad = []
    for rest in combinations(range(v1 + 1, H + 1), 4):
        P = (v1,) + rest
        if math.gcd(*P) != 1: continue
        hit = [j for j in (1, 4, 2, 3) if split_ok(P, j)]
        if hit: c[hit[0]] += 1
        else: c[0] += 1; bad.append((Fr(P[0], P[4]), P))
    bad.sort(); return c, bad[:30]
if __name__ == "__main__":
    H = int(sys.argv[1])
    with Pool(10) as pool: res = pool.map(work, [(v1, H) for v1 in range(1, H - 3)], chunksize=1)
    c = Counter(); bad = []
    for r in res: c += r[0]; bad += r[1]
    bad.sort(); n = sum(c.values())
    print(f"exact, primitive 5-prefixes <= {H}: {n}; closed by a split {n - c[0]} ({(n - c[0]) / n:.2%}); "
          f"first split that closes (order 1, 4, 2, 3): {dict(sorted(c.items()))}")
    print(f"   not closed: smallest v1/v5 = {bad[0][0]}; 30 smallest:", [(str(x), P) for x, P in bad[:30]])
