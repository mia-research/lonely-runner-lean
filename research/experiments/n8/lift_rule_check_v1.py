"""The lift (2026-09-24).  ds = n*M' u X, X the non-multiples of n.  Claim (derived by hand):
if flank f works for M' at index j0 < f, then flank n*f works for ds at some j = j0 + f*i,
0 <= i < n, as soon as some i avoids every x's bad set, where for x in X
    q0 = (x*(n*j0+1) mod n^2 f) div (n f),   Q(i) = (q0 + x*i) mod n,   bad iff Q in {0, n-1}.
Sufficient: sum of b(x) < n, b(x) = 2 if gcd(x,n)=1 else gcd(x,n).
Checks: (A) exact lift condition <=> flank n*f works at an index in j0's class mod f (both
directions, per (f, j0)); (B) the sufficient count implies the lift; (C) M = c-1 (|X| = 1,
n >= 3): every working (f, j0) of M' lifts."""
from itertools import combinations
from math import gcd
import random


def band(n, e, r):
    return e <= r <= (n - 1) * e


def works_at(n, ds, e, j):
    a = n * j + 1
    return all(band(n, e, (d * a) % (n * e)) for d in ds)


def lift_ok(n, X, f, j0):
    a0 = n * j0 + 1
    for i in range(n):
        if all(((x * a0) % (n * n * f) // (n * f) + x * i) % n not in (0, n - 1) for x in X):
            return True
    return False


def b(x, n):
    g = gcd(x, n)
    return 2 if g == 1 else g


random.seed(20260924)
for n in range(3, 11):
    A_bad = B_tested = B_bad = C_tested = C_bad = 0
    for _ in range(4000):
        r = random.randint(1, n - 2)          # number of multiples
        s = random.randint(1, n - 1 - r)      # number of non-multiples (s >= 1)
        Mp = sorted(random.sample(range(1, 30), r))
        X = sorted(random.sample([x for x in range(1, 30 * n) if x % n], s))
        ds = [n * m for m in Mp] + X
        for f in Mp:
            for j0 in range(f):
                if not works_at(n, Mp, f, j0):
                    continue
                direct = any(works_at(n, ds, n * f, j0 + f * i) for i in range(n))
                ex = lift_ok(n, X, f, j0)
                A_bad += direct != ex
                if sum(b(x, n) for x in X) < n:
                    B_tested += 1
                    B_bad += not direct
                if s == 1:
                    C_tested += 1
                    C_bad += not direct
    print(f"n={n}: (A) exact-condition mismatches {A_bad}; (B) count<n cases {B_tested}, lift fails {B_bad};"
          f" (C) M=c-1 cases {C_tested}, lift fails {C_bad}")
