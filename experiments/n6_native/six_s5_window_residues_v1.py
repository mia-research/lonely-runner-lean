#!/usr/bin/env python3
"""§5, cascade endings at an opening N of runner 4 or 5 (flank x), inside the first meeting window
(D T in [0, 1/6], D = v3 - v2). Reduced residue form, with m = 6N + 1 and residues mod 6x:
  C1  runner 1:            x <= v1 m mod 6x <= 5x
  C23 runners 2, 3 merged: x + D m <= v3 m mod 6x <= 5x      (x2 = x3 - D T, D T = D m/(6x))
  Cy  other fast runner y: x <= y m mod 6x <= 5x
Checks, for every ending: D T in [0, 1/6]; each condition holds; and over ALL openings N < x of the flank,
for sets in the window, that (C1 and C23 and Cy) is equivalent to the full residue test for all five
(exactness of the reduction where D m <= x, i.e. inside the window). Records the opening N and the
tightest condition (least slack in residue units). Exact integers."""
from fractions import Fraction as F
from collections import Counter
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c, m, ranks, laps, T, fr = l.rstrip("\n").split("\t")
    if c == "S5": rows.append((eval(s), F(T), int(fr)))
n = win = 0; ok = Counter(); Ns = Counter(); tight = Counter(); eq_checked = eq_bad = 0
for S, T, fr in rows:
    if fr not in (4, 5): continue
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    x = S[fr - 1]; y = v5 if fr == 4 else v4
    x6T = 6 * x * T; N = (x6T.numerator // x6T.denominator) // 6   # T = (6N+1)/(6x)
    assert F(6 * N + 1, 6 * x) == T
    n += 1; Ns[N] += 1
    mm = 6 * N + 1; M = 6 * x
    win += F(0) <= D * T <= F(1, 6)
    r1, r3, ry = (v1 * mm) % M, (v3 * mm) % M, (y * mm) % M
    c1 = x <= r1 <= 5 * x; c23 = x + D * mm <= r3 <= 5 * x; cy = x <= ry <= 5 * x
    ok[(c1, c23, cy)] += 1
    sl = {"C1": min(r1 - x, 5 * x - r1), "C23": min(r3 - x - D * mm, 5 * x - r3), "Cy": min(ry - x, 5 * x - ry)}
    tight[min(sl, key=sl.get)] += 1
    for j in range(x):                     # exactness of the reduction at every opening inside the window
        m2 = 6 * j + 1
        if D * m2 > x: continue            # D T <= 1/6
        full = all(x <= (d * m2) % M <= 5 * x for d in S)
        red = (x <= (v1 * m2) % M <= 5 * x) and (x + D * m2 <= (v3 * m2) % M <= 5 * x) and (x <= (y * m2) % M <= 5 * x)
        eq_checked += 1; eq_bad += full != red
print(f"§5 endings at runner 4 or 5: {n}; inside the first meeting window: {win}")
print(f"  (C1, C23, Cy) at the endpoint: {dict(ok)}")
print(f"  opening index N: {dict(sorted(Ns.items()))}")
print(f"  tightest condition: {dict(tight)}")
print(f"  reduction exact at in-window openings: checked {eq_checked}, mismatches {eq_bad}")
