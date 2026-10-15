#!/usr/bin/env python3
"""(1) Runner 1's first clear lap. The cascade starts at t0 = 1/(6 v1), runner 1's opening; runner 1 is clear on
[t0, 5 t0]. For every residual set ([1,40]) record v1*T (the endpoint's reading of runner 1): is the endpoint in
runner 1's first clear lap (v1 T <= 5/6)? List every exception with its BHK case and path.
(2) §5 endings at runner 4/5 outside the first meeting window: delta = frac(D T); the pair (2,3) is clear iff
x3 in [1/6,5/6] and (x3 - delta) mod 1 in [1/6,5/6]; check that this equals x3 in [1/6+delta, 5/6] when
delta <= 1/3, and [1/6, delta - 1/6] u [1/6 + delta, 5/6] when 1/3 < delta <= 2/3 (exact), and record delta.
Exact Fractions."""
from fractions import Fraction as F
from collections import Counter
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c, m, ranks, laps, T, fr = l.rstrip("\n").split("\t")
    rows.append((eval(s), c, eval(ranks), F(T), int(fr)))
def frac(x): return x - (x.numerator // x.denominator)
# (1)
exc = []; n = 0; bins = Counter()
for S, c, rk, T, fr in rows:
    n += 1; r = S[0] * T
    bins[min(int(r * 6), 6)] += 1
    if r > F(5, 6): exc.append((S, c, rk, str(r)))
print(f"(1) residual sets {n}; endpoint reading of runner 1, v1*T, by sixths: {dict(sorted(bins.items()))}")
print(f"    endpoints beyond runner 1's first clear lap (v1 T > 5/6): {len(exc)}")
for e in exc[:20]: print("     ", e)
# (2)
dl = Counter(); bad = 0; n2 = 0
for S, c, rk, T, fr in rows:
    if c != "S5" or fr not in (4, 5): continue
    D = S[2] - S[1]
    if D * T <= F(1, 6): continue
    n2 += 1; d = frac(D * T); x3 = frac(S[2] * T); x2 = frac(S[1] * T)
    direct = F(1, 6) <= x3 <= F(5, 6) and F(1, 6) <= x2 <= F(5, 6)
    if d <= F(1, 3): form = F(1, 6) + d <= x3 <= F(5, 6)
    elif d <= F(2, 3): form = (F(1, 6) <= x3 <= d - F(1, 6)) or (F(1, 6) + d <= x3 <= F(5, 6))
    else: form = None
    bad += form is not None and form != direct
    dl[min(int(d * 6), 5)] += 1
print(f"(2) §5 endings at 4/5 outside the first meeting window: {n2}; delta by sixths: {dict(sorted(dl.items()))}; "
      f"mismatches of the band-intersection form: {bad}")
