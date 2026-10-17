#!/usr/bin/env python3
"""Claim R (first stretch), EXACT: for a five-runner block F (positive integers) and a slow speed v1, is F lonely at 1/7
at some t in [1/(7 v1), 6/(7 v1)]?  Equivalently w = F/v1 lonely at some theta in [1/7, 6/7].  Exact integer band
arithmetic: time scaled by N = 7 lcm(F) * v1 ... we use the lonely intervals of F over one period (o7_exact) and
intersect with the stretch.  Reports, over families, the smallest ratio v2/v1 at which Claim R fails, and the failures.
Families: random bounded-ratio blocks; runs (n..n+4d); scaled tight patterns c(1,2,3,4,5)+o, c(1,3,4,5,9)+o; random
blocks with v2/v1 from 2 to 200."""
import math, random, sys
from fractions import Fraction as Fr
from collections import Counter
from o7_exact import lcm, inter
def lonely_F(F):
    M = lcm(F); N = 7 * M
    cur = None
    for v in F:
        q = M // v; B = [((7 * m + 1) * q, (7 * m + 6) * q) for m in range(v)]
        cur = B if cur is None else inter(cur, B, strict=False)
    return cur, N
def claimR(F, v1):
    iv, N = lonely_F(F)
    lo, hi = Fr(N, 7 * v1), Fr(6 * N, 7 * v1)       # stretch in scaled time (one period [0, N))
    return any(L <= hi and U >= lo for L, U in iv)
rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 11)
fails = []; tested = Counter()
def test(name, F, v1):
    F = tuple(sorted(F))
    if len(set(F)) < 5 or F[0] <= v1: return
    tested[name] += 1
    if not claimR(F, v1): fails.append((Fr(F[0], v1), name, v1, F))
for _ in range(3000):
    v2 = rnd.randint(10, 400); F = (v2, *sorted(rnd.sample(range(v2 + 1, 5 * v2), 4)))
    for r in (2, 3, 4, 6, 8, 12, 20, 50):
        v1 = max(1, v2 // r); test(f"random r={r}", F, v1)
for n in (20, 50, 100, 300):
    for d in (1, 2, 3, 5, 7):
        for v1 in range(1, n // 2):
            test("runs", (n, n + d, n + 2 * d, n + 3 * d, n + 4 * d), v1)
for pat in ((1, 2, 3, 4, 5), (1, 3, 4, 5, 9), (2, 3, 4, 5, 6), (1, 2, 3, 4, 6), (1, 2, 4, 5, 6)):
    for c in (10, 30, 100):
        for _ in range(5):
            o = [rnd.randint(0, 3) for _ in range(5)]
            F = tuple(c * p + oo for p, oo in zip(pat, o))
            for v1 in range(1, F[0] // 2 + 1): test("tightK", F, v1)
fails.sort()
print("tested:", dict(tested))
print(f"Claim R failures: {len(fails)}")
print("   smallest ratio v2/v1 among failures:", [(float(r), nm, v1, F) for r, nm, v1, F in fails[:5]])
print("   largest ratio v2/v1 among failures:", [(float(r), nm, v1, F) for r, nm, v1, F in fails[-15:]])
