"""v2: window 1 = [a_1, b_1] in general (a_1 > 1/8 when a frozen reading blocks t0); its cells are
((8m - 1)/(8 a_1), (8m + 1)/(8 b_1)), m >= 1, non-empty iff 8m (b_1 - a_1) < a_1 + b_1.  Below the lowest cell is
v <= 7/(8 a_1): v's first zone (lap 1) starts after a_1.  Above the last cell: v's zones at every lap are placed
or sized so none contains window 1; v >= (8 m_last + 1)/(8 b_1).
E945: why the would-pass positions mostly fail window 1 (2026-11-25).  Exact Fractions.
Window 1 of a six S is [1/8, b_1].  When no reading of S blocks t0 = 1/8 (no reading in (8m - 1, 8m + 1)), b_1 is the
first zone entry after t0 and a position v passes window 1 iff v lies in a cell (8m - 1, (8m + 1)/(8 b_1)), m >= 1
(E930 item 1).  Every cell lies above 7, and the cells end at the last lap m with 8m (b_1 - 1/8) < b_1 + 1/8.
For the crossers' positions of crosser_equality_cascade_v1 that fail window 1, sorted by: below 7 (under every cell);
above the last cell; between cells.  Also whether window 1 starts at t0.
"""
import pickle, glob, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('neighbour_mover_v1.py').read().split("rec = pickle.load(open('/Users")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
rows = []
for f in sorted(glob.glob('crosser_equality_v1_part*.pkl')): rows += pickle.load(open(f, 'rb'))
rows.sort()
step = int(sys.argv[1]); off = int(sys.argv[2]); c = Counter()
for idx, R0, closers, cls, att in rows[off::step]:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, _ = cascade(rs, E)
    for k1, cl in cls.items():
        if cl not in 'XN': continue
        k = k1 - 1; six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1); n = next(i for i, (a, b, o) in enumerate(ws) if a <= T <= b); a, b, o = ws[n]
        hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
        a1, b1, o1 = ws[0]
        c[(cl, 'window 1 starts at t0' if a1 == E else 'window 1 starts after t0')] += 0
        mlast = ceil((a1 + b1) / (8 * (b1 - a1))) - 1 if b1 > a1 else None
        for l, h, m in passes(a, b, lo, hi)[:20]:
            v = (l + h) / 2
            if n == 0 or passes_in(a1, b1, [(v - Fr(1, 10 ** 40), v + Fr(1, 10 ** 40))]): continue
            c[(cl, 'fails window 1')] += 1
            c[(cl, 'fails window 1', 'window 1 starts at t0' if a1 == E else 'window 1 starts after t0')] += 1
            if v <= Fr(7, 8) / a1: c[(cl, 'below the lowest cell: first zone after a_1')] += 1
            elif mlast is not None and v >= Fr(8 * mlast + 1) / (8 * b1): c[(cl, 'above the last cell')] += 1
            elif mlast is None: c[(cl, 'window 1 a point')] += 1
            else: c[(cl, 'between cells')] += 1
for kk, val in sorted(c.items(), key=str): print(val, '|', kk)
