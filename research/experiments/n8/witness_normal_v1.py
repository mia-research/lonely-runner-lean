"""WITNESS NORMALISATION, at every order.

Claim (from reach_mem + finite_check, both proved):  for distinct positive integers s_1..s_{n-1},
if SOME t has ||s_i t|| >= 1/n for all i, then some such t has the form

        t = A / (n * s)      with  s in S u {1},  A = 1 (mod n),  s <= A <= (n-1) s.

This is a SHARPENING of LRC's statement, not a restatement: it says the witness never needs to be
an arbitrary real, or even an arbitrary rational -- its denominator is n times one of the speeds.

Test: compare the exact interval sweep (ground truth, "is there any lonely t") against the
normalised search, at n = 4..9.  n <= 7 is where LRC is PROVED, so those orders check the
reduction itself, not the conjecture.
"""
from fractions import Fraction as F
from itertools import combinations
import random

def any_lonely_exact(S, n):
    """Ground truth: sweep the bad intervals of [1,n-1] in x-coords, x = n*t."""
    iv = []
    for s in S:
        m = 1
        while F(n*m - 1, s) < n - 1:
            if F(n*m + 1, s) > 1: iv.append((F(n*m - 1, s), F(n*m + 1, s)))
            m += 1
    iv.sort()
    r = F(1)
    for a, b in iv:
        if a < r: r = max(r, b)
        else: return True          # gap at r
    return r <= n - 1              # uncovered tail

def any_lonely_normalised(S, n):
    """Only look at t = A/(n s), A = 1 mod n, s in S u {1}."""
    for s in set(S) | {1}:
        M = n*s
        A = s + ((1 - s) % n)
        while A <= (n-1)*s:
            if all(min((sp*A) % M, M - (sp*A) % M) >= s for sp in S): return True
            A += n
    return False

rng = random.Random(20260919)
print(f"{'n':>3} {'arm':<26} {'profiles':>10} {'mismatch':>9} {'lonely':>8}")
for n in range(4, 10):
    k = n - 1
    # exhaustive small
    tot = mm = lon = 0
    for combo in combinations(range(1, 18), k):
        S = list(combo); tot += 1
        a, b = any_lonely_exact(S, n), any_lonely_normalised(S, n)
        if a != b: mm += 1
        lon += a
    print(f"{n:>3} {'exhaustive [1,17]':<26} {tot:>10,} {mm:>9,} {lon:>8,}")
    # random large
    tot = mm = lon = 0
    for _ in range(4000):
        S = sorted(rng.sample(range(1, 5000), k)); tot += 1
        a, b = any_lonely_exact(S, n), any_lonely_normalised(S, n)
        if a != b: mm += 1
        lon += a
    print(f"{n:>3} {'random [1,5000]':<26} {tot:>10,} {mm:>9,} {lon:>8,}")
