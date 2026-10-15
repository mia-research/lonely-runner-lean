#!/usr/bin/env python3
"""§8 exact step rules, checked on all §8 sets in six_cascade_observe_v1.tsv:
 (A) at opening 1 of v5 with 5 v1 < v5 < 7 v1, the three slowest are clear (v3 <= 3 v1);
 (B) for walks whose first move is (1,0) -> (5,1): the walk moves on to v4 iff 7 v4 > 5 v5, and then lands
     at opening 1 of v4; otherwise it stops at (5,1) unless another element blocks.
Exact Fractions."""
from fractions import Fraction as F
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c, m, ranks, laps = l.split("\t")[:5]
    if c == "S8": rows.append((eval(s), eval(ranks), eval(laps)))
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
A_n = A_bad = B_n = B_bad = 0
for S, rk, lp in rows:
    v1, v2, v3, v4, v5 = S
    if 5 * v1 < v5 < 7 * v1:
        t = F(7, 6 * v5); A_n += 1
        A_bad += any(cd(d * t) < F(1, 6) for d in (v1, v2, v3))
    if rk[:1] == (5,) and lp[:1] == (1,):
        B_n += 1
        moves_on = len(rk) >= 2 and rk[1] == 4 and lp[1] == 1
        B_bad += moves_on != (7 * v4 > 5 * v5)
print(f"(A) sets with 5v1 < v5 < 7v1: {A_n}; slow element in the way at 7/(6 v5): {A_bad}")
print(f"(B) walks starting (1,0)->(5,1): {B_n}; mismatches with 'moves on to (4,1) iff 7 v4 > 5 v5': {B_bad}")
