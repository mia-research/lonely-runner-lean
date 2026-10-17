#!/usr/bin/env python3
"""Provable split fold with the cluster window (EXACT Fractions). As o7_split_an_v1, plus a third gap bound for a fast
block F = (b + e_d) (b = min F, integer offsets e_d >= 0, c = max e):  `cluster_window` (Lean, O7Split) gives a window
of length w starting in [alpha, alpha + 1/b] whenever on [alpha, alpha + 1/b] the envelope gap is >= (b + c) w, i.e.
with laps m_d fixed:  max_d (e_d t - m_d) - min_d (e_d t - m_d) <= 5/7 - (b + c) w.  For each lap vector m this holds
on an interval I_m (pairwise linear constraints); the admissible alpha are [lo_m, hi_m - 1/b].  The offsets are
periodic with period 1/g (g = gcd of the e_d), so the admissible set is periodic and
   G_cluster(F) = (longest gap of the admissible alpha set) + 1/b + w.
Gap calculus: G(F) = min(cluster, stretch recursion from G(F[1:])), G(single u) = 2/(7u) + 2w.  Cluster bound only
for e_max/g <= EMAX (lap vectors enumerated).  Reports coverage over primitive prefixes <= H and the not-closed set."""
import math, sys
from fractions import Fraction as Fr
from itertools import combinations, product
from collections import Counter
from functools import lru_cache
from multiprocessing import Pool
EMAX = 24
def cluster_G(F, w):
    b = F[0]; e = [d - b for d in F]; c = e[-1]; g = 0
    for x in e: g = math.gcd(g, x)
    if g == 0 or c // g > EMAX: return None
    per = Fr(1, g); thr = Fr(5, 7) - (b + c) * w; ilen = Fr(1, b)
    if thr < 0: return None
    adm = []
    ranges = [range(0, ed // g + 2) if ed else range(0, 1) for ed in e]
    for m in product(*ranges):
        lo, hi = Fr(-10**9), Fr(10**9)
        for i in range(len(e)):
            for j in range(len(e)):
                if i == j: continue
                k = e[i] - e[j]; rhs = thr + m[i] - m[j]   # k t <= rhs
                if k > 0: hi = min(hi, rhs / k)
                elif k < 0: lo = max(lo, rhs / k)
                elif rhs < 0: lo, hi = 1, 0
        lo = max(lo, Fr(-1)); hi = min(hi, per + 1)
        if hi - ilen >= lo: adm.append((lo, hi - ilen))
    if not adm: return None
    # periodic union over [0, per): shift intervals into a window and merge
    iv = []
    for lo, hi in adm:
        for s in (-per, 0, per):
            iv.append((lo + s, hi + s))
    iv.sort(); merged = []
    for lo, hi in iv:
        if merged and lo <= merged[-1][1]: merged[-1] = (merged[-1][0], max(merged[-1][1], hi))
        else: merged.append((lo, hi))
    gaps = [merged[i + 1][0] - merged[i][1] for i in range(len(merged) - 1)
            if merged[i][1] < per + per and merged[i + 1][0] > -per]
    if any(hi - lo >= per for lo, hi in merged): gmax = Fr(0)
    else: gmax = max([x for x in gaps if x > 0], default=Fr(0))
    return gmax + ilen + w
def G_bound(F, w):
    best = cluster_G(F, w) if len(F) > 1 else None
    if len(F) == 1: return Fr(2, 7 * F[0]) + 2 * w
    inner = G_bound(F[1:], w)
    if inner is not None and Fr(5, 7 * F[0]) >= inner:
        s = Fr(2, 7 * F[0]) + 2 * inner
        best = s if best is None else min(best, s)
    return best
def closes(P):
    w = Fr(3, 28 * P[4])
    for j in range(1, 5):
        W = Fr(5, 7 * P[0]) if j == 1 else 2 * (Fr(1, j + 1) - Fr(1, 7)) / P[j - 1]
        G = G_bound(P[j:], w)
        if G is not None and W >= G: return j
    return 0
def work(args):
    v1, H = args; c = Counter(); low = []
    for rest in combinations(range(v1 + 1, H + 1), 4):
        P = (v1,) + rest
        if math.gcd(*P) != 1: continue
        j = closes(P); c[j] += 1
        if j == 0: low.append((Fr(P[0], P[4]), P))
    low.sort(); return c, low[:20]
if __name__ == "__main__":
    H = int(sys.argv[1])
    with Pool(10) as pool: res = pool.map(work, [(v1, H) for v1 in range(1, H - 3)], chunksize=1)
    c = Counter(); low = []
    for r in res: c += r[0]; low += r[1]
    low.sort(); n = sum(c.values())
    print(f"exact, provable split fold + cluster window, primitive prefixes <= {H}: {n}; closed {n - c[0]} "
          f"({(n - c[0]) / n:.2%}); by split {dict(sorted(c.items()))}")
    print(f"   not closed: smallest v1/v5 {low[0][0] if low else None}; 20 smallest:", [(str(x), P) for x, P in low[:20]])
