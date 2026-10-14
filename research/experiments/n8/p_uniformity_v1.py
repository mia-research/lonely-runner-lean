#!/usr/bin/env python3
"""Is the p=163 sector argument a METHOD or a one-off?

The n=8 goal is an ANALYTIC proof, so the point here is NOT to decide cells at 27
primes by computation -- that is the search, in cheaper clothes.  The point is to
learn whether the quantities the p=163 argument runs on are FORMULAS in p:

    h(p)      = (p-1) // 8                      arc half-width
    |A|       = 2h+1                            arc size
    U_min(x)  = p - max_{|W|=x} |union_w M[w]|  classes x coarse speeds must miss
    f(8,p)    = min x with U_min(x) = 0         dilates needed to cover Z/p
    maxD(p)   = max over odd pairs of #classes the pair fully covers

The x=5 sector argument needs the odd pair to fully cover every class the coarse
speeds miss, and uses |D| >= U_min(5) as a necessary filter.  If U_min(5) > maxD
for all large p, the filter alone closes the sector and the exhaustive coverability
search is not needed -- that would be an analytic argument with finitely many
exceptional primes.  At p=163 it does NOT (U_min(5)=12, maxD=27).  This measures
both sides as functions of p.

All integer arithmetic; no floats on the signal path.
"""
import sys
from itertools import combinations

S27 = [31,37,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,
       137,139,149,151,157,163]          # Rosenfeld's 27 primes (41 absent)
n = 8

def masks(p):
    h = (p - 1) // n
    A = {s % p for s in range(-h, h + 1)}
    W = list(range(1, (p - 1) // 2 + 1))          # M[-w] = M[w] since A = -A
    M = {}
    for w in W:
        m = 0
        for r in range(p):
            if (r * w) % p in A:
                m |= 1 << r
        M[w] = m
    return h, len(A), W, M

def max_union(p, W, M, x, arc):
    """max |union of x dilates|; WLOG the set contains w=1 (scale invariance)."""
    rest = [w for w in W if w != 1]
    best = [M[1].bit_count() if x == 1 else -1]
    if x == 1:
        return best[0]
    def rec(u, i, depth):
        if depth == x:
            c = u.bit_count()
            if c > best[0]: best[0] = c
            return
        if u.bit_count() + (x - depth) * arc <= best[0]:
            return                                  # bound: each dilate adds <= |A|
        for k in range(i, len(rest)):
            rec(u | M[rest[k]], k + 1, depth + 1)
    rec(M[1], 0, 1)
    return best[0]

def f_cover(p, W, M):
    """min number of dilates covering Z/p.  Exact: branch on the lowest uncovered r."""
    FULL = (1 << p) - 1
    by_r = [[w for w in W if (M[w] >> r) & 1] for r in range(p)]
    arc = M[1].bit_count()
    for lim in range(1, 12):
        def rec(u, d):
            rem = FULL & ~u
            if rem == 0: return True
            if d == lim: return False
            if rem.bit_count() > (lim - d) * arc: return False   # counting bound
            lb = (rem & -rem).bit_length() - 1
            return any(rec(u | M[w], d + 1) for w in by_r[lb])
        if rec(0, 0): return lim
    return None

def max_D(p):
    """max over pairs of odd speeds of #classes the pair FULLY covers (all 4 targets)."""
    N, H = n * p, n * p // 2
    odd = [v for v in range(1, H + 1) if v % 2 == 1 and v % p != 0]
    B = {}
    for v in odd:
        bs = [0, 0, 0, 0]
        for i, r in enumerate(range(1, p + 1)):
            for t in range(4):
                j = r + p * t
                rr = (j * v) % N
                if rr < p or rr > N - p:
                    bs[t] |= 1 << i
        B[v] = bs
    best = 0
    for v1, v2 in combinations(odd, 2):
        a, b = B[v1], B[v2]
        D = (a[0]|b[0]) & (a[1]|b[1]) & (a[2]|b[2]) & (a[3]|b[3])
        c = D.bit_count()
        if c > best: best = c
    return len(odd), best

if __name__ == "__main__":
    ps = [int(a) for a in sys.argv[1:]] or S27
    print(f"{'p':>4} {'h':>4} {'|A|':>4} {'dens':>9} "
          f"{'Umin1':>6} {'Umin2':>6} {'Umin3':>6} {'Umin4':>6} {'Umin5':>6} "
          f"{'f(8,p)':>7} {'#odd':>5} {'maxD':>5} {'Umin5-maxD':>11}")
    for p in ps:
        h, arc, W, M = masks(p)
        U = [p - max_union(p, W, M, x, arc) for x in range(1, 6)]
        f = f_cover(p, W, M)
        nodd, mD = max_D(p)
        print(f"{p:>4} {h:>4} {arc:>4} {str(arc)+'/'+str(p):>9} "
              + " ".join(f"{u:>6}" for u in U)
              + f" {str(f):>7} {nodd:>5} {mD:>5} {U[4]-mD:>11}", flush=True)
