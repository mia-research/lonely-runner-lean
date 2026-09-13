"""
Does the procedure return at orders other than n = 8?

MANUSCRIPT section 7.3 reports zero failures over every integer arrangement with
0 = v_1 < ... < v_8 <= 40, and section 9 says plainly that this "says nothing about other
orders". This script says something about other orders.

DIFFERENCE FROM THE PAPER'S SWEEP. That record pins a runner at 0 (Rosenfeld's
formulation). This one does not: speeds are n DISTINCT POSITIVE integers with gcd 1, which
is the framework's own setting. The two families are related by the standard reduction but
are not the same enumeration, so the counts are not comparable line for line.

THE DECISION PROCEDURE IS EXACT, and it is the Boundary Set Method, not a sample.
For runner i with readings s = a/b, the in-the-way zone of lap k is the OPEN interval
    ( (n k - 1)/(n s), (n k + 1)/(n s) )
so the procedure returns iff the open zones fail to cover the CLOSED window
[1/n, (n-1)/n]. The complement of finitely many open intervals inside a closed interval has
its endpoints among the zone endpoints and the window endpoints, so testing exactly those
candidates is complete -- no sampling, no grid, no tolerance.

Zones are never merged: two zones that touch leave their shared endpoint CLEAR, and that
endpoint is a candidate like any other. Fractions throughout.
"""
import sys, itertools
from fractions import Fraction as F
from math import gcd

def readings(v, i, n):
    d = sorted(abs(v[j] - v[i]) for j in range(n) if j != i)
    dmin = d[0]
    return [F(x, dmin) for x in d[1:]]

def zones(s, n, lo, hi):
    """Open in-the-way zones of reading s meeting the window [lo, hi]."""
    out = []
    k = 0
    while True:
        a = F(n * k - 1, n) / s
        b = F(n * k + 1, n) / s
        if a > hi:
            break
        if b > lo:
            out.append((a, b))
        k += 1
    return out

def returns(v, i, n):
    lo, hi = F(1, n), F(n - 1, n)
    Z = []
    for s in readings(v, i, n):
        Z.extend(zones(s, n, lo, hi))
    cands = {lo, hi}
    for a, b in Z:
        if lo <= a <= hi:
            cands.add(a)
        if lo <= b <= hi:
            cands.add(b)
    for u in sorted(cands):
        if not any(a < u < b for a, b in Z):
            return u
    return None

def sweep(n, V):
    tot = fail = 0
    worst = F(0)
    worst_at = None
    for v in itertools.combinations(range(1, V + 1), n):
        g = 0
        for x in v:
            g = gcd(g, x)
        if g != 1:
            continue
        for i in range(n):
            tot += 1
            u = returns(list(v), i, n)
            if u is None:
                fail += 1
                if fail <= 3:
                    print(f"    FAILURE n={n} v={v} runner={i}", flush=True)
            elif u > worst:
                worst, worst_at = u, (v, i)
    return tot, fail, worst, worst_at

if __name__ == "__main__":
    print("exhaustive: n distinct positive integer speeds, gcd 1, NO runner pinned at 0")
    print("exact Fractions; Boundary Set Method; open zones, endpoints clear\n")
    print(f"{'n':>3} {'V':>4} {'instances':>11} {'failures':>9} {'worst u':>12} "
          f"{'window end':>11}")
    print("-" * 60)
    for n, V in [(5, 34), (6, 26), (7, 21), (8, 18), (9, 16), (10, 15)]:
        tot, fail, worst, at = sweep(n, V)
        print(f"{n:>3} {V:>4} {tot:>11} {fail:>9} {str(worst):>12} "
              f"{str(F(n-1, n)):>11}", flush=True)
        if at:
            print(f"        worst at v={at[0]} runner={at[1]}", flush=True)
