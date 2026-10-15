#!/usr/bin/env python3
"""§5 observations, [1,40] (from six_cascade_observe_v1.tsv). D = v3 - v2, k = v1/D.
(A) k >= 3 (BHK Case 5.1): runners 2 and 3 read within 1/6 when frac(D t) in [0, 1/6] (just after a meeting,
    BHK (31)). Fraction of cascade endpoints with that property, against all lonely openings of the set.
(B) all k, endings at runner 4 or 5: the 123-gap containing T (maximal interval around T on which runners
    1, 2, 3 are clear, computed exactly from their bands). Compare its length G with Lemma 4's 2/(3 v4)
    (then runners 4, 5 have a lonely instant in it) and with half a lap of runner 3, 1/(2 v3) (BHK Case 5.1's
    gaps). Same for all lonely openings at runners 4, 5 (control). Exact Fractions."""
from fractions import Fraction as F
from collections import Counter
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c, m, ranks, laps, T, fr = l.rstrip("\n").split("\t")
    if c == "S5": rows.append((eval(s), F(T), int(fr)))
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def frac(x): return x - (x.numerator // x.denominator)
def band(d, t):
    # clear band of d containing t: [(K + 1/6)/d, (K + 5/6)/d], K = floor(d t)
    K = (d * t).numerator // (d * t).denominator
    return F(6 * K + 1, 6 * d), F(6 * K + 5, 6 * d)
def gap123(S, t):
    lo, hi = F(0), F(10**9)
    for d in S[:3]:
        a, b = band(d, t); lo, hi = max(lo, a), min(hi, b)
    return hi - lo
def lonely_openings(S, flanks):
    out = []
    for b in flanks:
        for j in range(b):
            t = F(6 * j + 1, 6 * b)
            if all(cd(d * t) >= F(1, 6) for d in S): out.append(t)
    return out
A = [0, 0, 0.0]; B = Counter(); Bc = Counter(); nb = nbc = 0
for S, T, fr in rows:
    v1, v2, v3, v4, v5 = S; D = v3 - v2; k = v1 // D
    if k >= 3:
        L = lonely_openings(S, S)
        A[0] += 1; A[1] += F(0) <= frac(D * T) <= F(1, 6)
        A[2] += sum(F(0) <= frac(D * t) <= F(1, 6) for t in L) / len(L)
    if fr in (4, 5):
        G = gap123(S, T); nb += 1
        B[("G >= 2/(3 v4)", G >= F(2, 3 * v4))] += 1; B[("G >= 1/(2 v3)", G >= F(1, 2 * v3))] += 1
        for t in lonely_openings(S, (v4, v5)):
            Gt = gap123(S, t); nbc += 1
            Bc[("G >= 2/(3 v4)", Gt >= F(2, 3 * v4))] += 1; Bc[("G >= 1/(2 v3)", Gt >= F(1, 2 * v3))] += 1
print(f"(A) k >= 3 sets: {A[0]}; cascade endpoint just after a 2-3 meeting (frac(D T) in [0,1/6]): {A[1]} "
      f"({A[1]/A[0]:.3f}); control (all lonely openings): {A[2]/A[0]:.3f}")
print(f"(B) §5 endings at runner 4 or 5: {nb}")
for key in [("G >= 2/(3 v4)", True), ("G >= 1/(2 v3)", True)]:
    print(f"    {key[0]}: cascade endpoints {B[key]}/{nb} ({B[key]/nb:.3f}); all lonely openings at 4, 5: {Bc[key]}/{nbc} ({Bc[key]/nbc:.3f})")
