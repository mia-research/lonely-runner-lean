"""Robust windows for fast blocks: is (longest run with no common clear point at 1/8) x min(F) bounded?

For a block F of f runners, the worst window of any starting phase is the longest component of the
union of open blocked zones ((k - 1/8)/d, (k + 1/8)/d), over one full period 1/gcd(F); touching
zones leave their endpoint clear (BSM).  kappa_f = sup over F of that length times min F.  If finite,
every window of length kappa_f/min F holds a point where the block is clear, whatever its phase, and
the fast-block rule works for blocks of size f.  Exhaustive over f-subsets of [1,B], exact.
"""
import sys
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce
def longest_blocked(Fs):
    g = reduce(gcd, Fs); P = F(1, g)
    z = sorted((F(8 * k - 1, 8 * d), F(8 * k + 1, 8 * d)) for d in Fs for k in range(0, d // g + 2))
    best = F(0); lo, hi = z[0]
    for a, b in z[1:]:
        if a < hi: hi = max(hi, b)
        else: best = max(best, hi - lo); lo, hi = a, b
    return max(best, hi - lo)
for f, B in ((2, 60), (3, 40), (4, 26), (5, 20), (6, 18)):
    best = max((longest_blocked(Fs) * min(Fs), Fs) for Fs in combinations(range(1, B + 1), f) if reduce(gcd, Fs) == 1)
    print(f"f={f}, primitive blocks in [1,{B}]: kappa >= {best[0]} = {float(best[0]):.4f} at {best[1]}", flush=True)

# growth along consecutive blocks (N, N+1, ..., N+f-1): if kappa grows with N, no robust window exists
print("consecutive blocks, (longest blocked run) x N:")
for f in (3, 4, 5, 6):
    row = []
    for N in (20, 40, 80, 160):
        row.append(f"N={N}: {float(longest_blocked(tuple(range(N, N + f))) * N):.2f}")
    print(f"  f={f}: " + ";  ".join(row), flush=True)
