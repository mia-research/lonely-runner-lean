#!/usr/bin/env python3
"""Owner's question on (1..5, 16, 64, 720) and (1..7, 16): for each runner as subject, threshold 1/8, the cascade's
earliest lonely instant (exact; start at 1/(8 d_min), move to the latest next opening of the runners in the way;
MomentIterationN.move) with its move count, checked against an exhaustive scan of every flank opening (k + 1/8)/b,
k < b, over one period (earliest certificate). Also the flank whose opening it is."""
from fractions import Fraction as F
def frac(z): return z - (z.numerator // z.denominator)
def cd(z): f = frac(z); return min(f, 1 - f)
thr = F(1, 8)
def cascade(ds):
    t = thr / min(ds); moves = 0
    while True:
        blk = [d for d in ds if cd(d * t) < thr]
        if not blk: return t, moves
        t = max((((d * t - thr).numerator // (d * t - thr).denominator) + 1 + thr) / d for d in blk); moves += 1
def exhaustive(ds):
    return min((k + thr) / b for b in ds for k in range(b) if all(cd(d * (k + thr) / b) >= thr for d in ds))
for sp in [(1, 2, 3, 4, 5, 16, 64, 720), (1, 2, 3, 4, 5, 6, 7, 16)]:
    print(f"== {sp}")
    for s in sp:
        ds = [abs(d - s) for d in sp if d != s]
        T, m = cascade(ds); E = exhaustive(ds)
        fl = [d for d in ds if frac(d * T) == thr]
        print(f"   subject {s:4d}: cascade T = {T} ({float(T):.5f}), {m} moves, flank {fl}; exhaustive earliest {E}; agree {T == E}")
