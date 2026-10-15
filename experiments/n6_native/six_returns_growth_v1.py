#!/usr/bin/env python3
"""Every return in the walk (immediate and delayed), all residual sets [1,40], against ChainBounds:
x leaves at its lap-P opening t; after m moves (laps Q_1..Q_m) the walk is at t' where x is in the way
(x then returns at lap P'). Proved: t'/t > L = (6P+5)/(6P+1) (return_growth) and
t'/t < U = prod (6Q_j+1)/(6Q_j-1) (move_growth, iterated). Records the shape (P, intervening laps, P'),
whether P' = P + 1, and where t'/t sits: position (t'/t - L)/(U - L) in [0,1]. Exact Fractions."""
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
            if best is None or o > best[0]: best = (o, d, N)
        t = best[0]; states.append((best[1], best[2], t))
shapes = Counter(); pp1 = 0; n = 0; viol = 0; pos_bins = Counter(); minpos = (2, None)
for S in rows:
    st = walk(S)
    last = {}
    for i, (x, P, t) in enumerate(st):
        if x in last:
            j = last[x]; Pold, told = st[j][1], st[j][2]
            mids = st[j + 1:i]               # intervening moves; t' = time of the state before the return
            tprime = st[i - 1][2]
            Qs = tuple(q for _, q, _ in mids)
            L = F(6 * Pold + 5, 6 * Pold + 1)
            U = F(1)
            for q in Qs: U *= F(6 * q + 1, 6 * q - 1)
            g = tprime / told
            n += 1; viol += not (L < g < U)
            pos = (g - L) / (U - L)
            pos_bins[min(int(pos * 5), 4)] += 1
            if pos < minpos[0]: minpos = (pos, (S, Pold, Qs, P))
            shapes[(Pold, Qs, P)] += 1; pp1 += P == Pold + 1
        last[x] = i
print(f"returns: {n}; violations of L < t'/t < U: {viol}; return lap P' = P + 1: {pp1}")
print("  position of t'/t between the bounds (fifths, 0 = at the lower bound L):", dict(sorted(pos_bins.items())))
print(f"  tightest against L: position {float(minpos[0]):.4f} at {minpos[1]}")
print("  shapes (P, intervening laps, P') most common:", shapes.most_common(12))
