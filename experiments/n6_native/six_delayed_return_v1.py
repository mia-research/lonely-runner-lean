#!/usr/bin/env python3
"""Delayed returns of shape x@1 -> y@1 -> z@1 -> x@2 (laps (1,1,1,2)), all residual sets [1,40]. Exact check:
x is in the way at z's opening 1 near lap 2 iff 11 z < 7 x < 13 z (reading 7x/(6z) within 1/6 of 2)."""
from fractions import Fraction as F
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
        t = best[0]; states.append((best[1], best[2]))
n = bad = 0
for S in rows:
    st = walk(S)
    for i in range(len(st) - 3):
        (x, a), (y, b), (z, c), (w, d) = st[i:i + 4]
        if (a, b, c, d) == (1, 1, 1, 2) and w == x and len({x, y, z}) == 3:
            n += 1; bad += not (11 * z < 7 * x < 13 * z)
print(f"delayed returns x@1 -> y@1 -> z@1 -> x@2: {n}; violations of 11 z < 7 x < 13 z: {bad}")
