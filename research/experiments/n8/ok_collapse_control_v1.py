#!/usr/bin/env python3
"""CONTROL for the near-zero collapse window.  Exact Fraction.

The near-0 window (0, 1/(2 e1)) searches, after the eight j/8 shifts, a set of measure
4/e1 -- mean 0.30 of the circle.  A 98% hit rate on 30% of the circle proves nothing
unless a window of the SAME LENGTH placed elsewhere does worse.  That is the control.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce

LVL = F(1, 8)
def nrm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1 - f)
def blocked(e, t):
    return {j for j in range(8) if nrm(F(e) * (t + F(j, 8))) < LVL}

def search(T, lo, hi):
    """exhaustive over cells of (lo,hi); all breakpoints are m/(8e).  Returns a witness."""
    cuts = {lo, hi}
    for e in T:
        for m in range(int(lo * 8 * e), int(hi * 8 * e) + 2):
            c = F(m, 8 * e)
            if lo < c < hi: cuts.add(c)
    cs = sorted(cuts)
    for i in range(len(cs) - 1):
        t = (cs[i] + cs[i + 1]) / 2
        hit = set()
        for e in T: hit |= blocked(e, t)
        if len(hit) < 8:
            j = min(set(range(8)) - hit)
            return t + F(j, 8)
    return None

tuples = [T for T in combinations(range(1, 21), 7)
          if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
tuples = tuples[::max(1, len(tuples) // 900)]
n = len(tuples)
print(f"{n} Case-2 tuples from [1..20]; window length L = 1/(2 e1) in every row.\n")
print("  offset c            hit rate   verified")
for name, cf in (("0  (the collapse window)", lambda L: F(0)),
                 ("L        ", lambda L: L),
                 ("2L       ", lambda L: 2 * L),
                 ("1/16 - L/2", lambda L: F(1, 16) - L / 2),
                 ("1/8 - L  ", lambda L: F(1, 8) - L)):
    hits = ok = 0
    for T in tuples:
        e1 = max(e for e in T if e % 2)
        L = F(1, 2 * e1)
        c = cf(L)
        if c < 0: c = F(0)
        w = search(list(T), c, c + L)
        if w is not None:
            hits += 1
            if all(nrm(F(e) * w) >= LVL for e in T): ok += 1
    print(f"  {name:<20} {hits:>5} ({100*hits//n:>3}%)   {ok}")
