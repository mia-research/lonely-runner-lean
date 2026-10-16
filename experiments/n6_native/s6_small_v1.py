#!/usr/bin/env python3
"""Observation. §6 open cases.
(A) D < 15, all residue pairs (a, b) = (v1 mod D, v4 mod D) with D not | a: the set P of runner-4 phases b k / D over the k
with runner-1 phase a k / D in [1/6, 5/9]. The after-window argument needs every closed half arc to contain a point of P,
i.e. every circular gap of P at most 1/2. Same with the before window (runner 1 in [4/9, 5/6]). Report the (D, a, b) that
pass with the after window, with either window (union of the two point sets is NOT what is needed: each window has its
own arc; reported separately), and the failing ones.
(B) For the failing residue classes, and for directions 0, +-1 at any D: how many actual §6 sets <= 40 fall there."""
from fractions import Fraction as F
from collections import Counter
def gaps_ok(pts):
    if not pts: return False
    s = sorted(set(pts)); g = [s[i + 1] - s[i] for i in range(len(s) - 1)] + [1 - s[-1] + s[0]]
    return max(g) <= F(1, 2)
res = Counter(); fails = []
for D in range(2, 15):
    for a in range(1, D):
        for b in range(D):
            after = [F(b * k % D, D) for k in range(D) if F(1, 6) <= F(a * k % D, D) <= F(5, 9)]
            before = [F(b * k % D, D) for k in range(D) if F(4, 9) <= F(a * k % D, D) <= F(5, 6)]
            if gaps_ok(after): res["after window passes"] += 1
            elif gaps_ok(before): res["before window passes"] += 1
            else: res["neither"] += 1; fails.append((D, a, b))
print("(A) residue classes (D < 15):", dict(res))
fc = Counter((D, ) for D, a, b in fails)
print("    failing classes per D:", sorted(fc.items()))
print("    examples:", fails[:20])
