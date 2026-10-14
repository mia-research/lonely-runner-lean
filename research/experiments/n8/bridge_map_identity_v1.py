"""
bridge_map_identity_v1.py -- n=8.  Verifies the exact characterisation that makes
k = b + r*L the (only) correct fibre->safe-point map, and shows precisely where
the bad-set definition of section 5.1 is exact and where it is conservative.

Claim under test.  For b in [0,L) and r in Z/nZ put k = b + r*L, and for each
speed e write e*b = t_e*L + s_e with t_e = floor(e*b/L), s_e = (e*b) mod L.  Then

    (e*k) mod (n*L) = L * ((t_e + e*r) mod n) + s_e ,

so k is a safe point  <=>  for every e in E,
        u_e := (t_e + e*r) mod n  is in {1,...,n-2},
     or u_e = n-1 and s_e = 0.

And r in bad(e,t_e,n)  <=>  u_e in {0, n-1}.  Hence

    r not covered by ANY e in E (all runners)  ==>  k is a safe point,

with the converse failing only in the boundary case u_e = n-1, s_e = 0.

Exact integer arithmetic.
"""

from math import gcd, lcm
from itertools import combinations
import random

n = 8


def sol(e, j):
    return {r for r in range(n) if (e * r) % n == j % n}


def bad(e, t):
    return sol(e, -t) | sol(e, -(t + 1))


def main(Lmax=2000, per_L=3, samples=300, seed=7):
    rng = random.Random(seed)
    tuples = pairs = mismatch = 0
    implication_checked = implication_fail = 0
    boundary_seen = 0
    for L in range(n, Lmax + 1, n):
        divs = [d for d in range(1, L + 1) if L % d == 0]
        if len(divs) < 7:
            continue
        cs = list(combinations(divs, 7))
        rng.shuffle(cs)
        got = 0
        for c in cs:
            if got >= per_L:
                break
            if not any(x % n == 0 for x in c):
                continue
            g = 0
            for x in c:
                g = gcd(g, x)
            if g != 1:
                continue
            l = 1
            for x in c:
                l = lcm(l, x)
            if l != L:
                continue
            got += 1
            tuples += 1
            N = n * L
            for _ in range(samples):
                b = rng.randrange(0, L)
                r = rng.randrange(0, n)
                k = b + r * L
                if not (1 <= k <= N - 1):
                    continue
                true_safe = all(L <= (e * k) % N <= (n - 1) * L for e in c)
                pred = True
                bnd = False
                for e in c:
                    t = (e * b) // L
                    s = (e * b) % L
                    u = (t + e * r) % n
                    if u == 0 or (u == n - 1 and s != 0):
                        pred = False
                        break
                    if u == n - 1:
                        bnd = True
                pairs += 1
                if pred != true_safe:
                    mismatch += 1
                # the sufficient condition actually used by the framework
                uncovered_all = all(r not in bad(e, (e * b) // L) for e in c)
                if uncovered_all:
                    implication_checked += 1
                    if not true_safe:
                        implication_fail += 1
                if bnd and true_safe:
                    boundary_seen += 1
    print(f"tuples                                  : {tuples}")
    print(f"(b,r) pairs checked                     : {pairs}")
    print(f"mismatches of the exact characterisation: {mismatch}")
    print(f"pairs with r uncovered by ALL of E      : {implication_checked}")
    print(f"  ... of which k is NOT a safe point    : {implication_fail}")
    print(f"safe k hitting the u = n-1, s_e = 0 boundary (bad-set is "
          f"conservative there): {boundary_seen}")


if __name__ == "__main__":
    main()
