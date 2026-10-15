#!/usr/bin/env python3
"""Exceptions and outliers among the 1,188 returns ([1,40]). Exact Fractions throughout.
Notation: x leaves at its lap-P opening t; intervening moves j = 1..m with setters d_j at laps Q_j, each
caught at depth delta_j = Q_j - d_j * t_{j-1} in (-1/6, 1/6) (positive = before the integer); growth of move
j is (Q_j + 1/6)/(Q_j - delta_j). At t' (the state before the return) x reads (P + 1/6) * g, g = t'/t,
and returns at lap P' = the integer within 1/6 of that.
(1) Exceptions P' >= P + 2: check P' = round((P + 1/6) g) and that g > (6P + 11)/(6P + 1) (the growth that
    carries x past lap P + 1); list m, laps, g, and how many all-lap-1 moves that growth needs.
(2) Outliers: returns in the top fifth of the window (near U) and the bottom fifth (near L): mean of the
    setter depths delta_j (near U predicted: delta_j near 1/6, every setter caught at the edge), and x's
    depth at t', P' - x t' (near L predicted: x just entering its blocked zone, depth near 1/6 from below)."""
from fractions import Fraction as F
from collections import Counter
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def walk(S):
    t = F(1, 6 * S[0]); states = []
    while True:
        blk = [d for d in S if cd(d * t) < F(1, 6)]
        if not blk: return states
        best = None
        for d in blk:
            N = round(d * t); o = F(6 * N + 1, 6 * d)
            if best is None or o > best[0]: best = (o, d, N, N - d * t)
        states.append((best[1], best[2], best[0], best[3], t)); t = best[0]
exc = []; exc_ok = 0; top = []; bot = []
for S in rows:
    st = walk(S)   # (setter, lap, new time, depth, time before)
    last = {}
    for i, (x, P2, t2, dep, tb) in enumerate(st):
        if x in last:
            j = last[x]; P, t = st[j][1], st[j][2]
            mids = st[j + 1:i]; tprime = tb
            g = tprime / t
            L = F(6 * P + 5, 6 * P + 1); U = F(1)
            for _, q, _, _, _ in mids: U *= F(6 * q + 1, 6 * q - 1)
            pos = (g - L) / (U - L)
            xread = (P + F(1, 6)) * g
            if P2 >= P + 2:
                ok = round(xread) == P2 and g > F(6 * P + 11, 6 * P + 1)
                exc_ok += ok
                exc.append((S, P, tuple(q for _, q, _, _, _ in mids), P2, float(g), float(F(6 * P + 11, 6 * P + 1))))
            depths = [float(d) for _, _, _, d, _ in mids]
            xdepth = float(P2 - xread)
            if pos >= F(4, 5): top.append((sum(depths) / len(depths), xdepth, S))
            if pos < F(1, 5): bot.append((sum(depths) / len(depths), xdepth, S))
        last[x] = i
print(f"(1) exceptions P' >= P+2: {len(exc)}; explained exactly (P' = nearest integer to (P+1/6)g AND g > (6P+11)/(6P+1)): {exc_ok}")
sh = Counter((P, laps, P2) for _, P, laps, P2, _, _ in exc)
print("    shapes (P, intervening laps, P'):", sh.most_common(8))
print("    examples (set, P, laps, P', g, threshold):", exc[:4])
import statistics as st_
for name, grp in (("top fifth (near U)", top), ("bottom fifth (near L)", bot)):
    md = [a for a, _, _ in grp]; xd = [b for _, b, _ in grp]
    print(f"(2) {name}: {len(grp)} returns; mean setter depth {st_.mean(md):.3f} (max possible 1/6 = 0.167); "
          f"x's depth at t' (P' - x t'): mean {st_.mean(xd):.3f}, range [{min(xd):.3f}, {max(xd):.3f}]")
