"""E946: class-N readings against the cascade's last setter (2026-11-25).  Exact Fractions.
For each gate crosser (crosser_equality_v1 pickles): the landing's kind (at an exit of the last setter strictly inside
a six-window of the other six, or at a six-window opening), the last setter's rank, and for each reading its class.
Question: is a class-N reading always the last setter, and how is the last setter classed when it is not N.
For each N reading that is not the last setter, through the cascade at its first escaping position: the moved
arrangement's last setter and the step at which the path first differs.
"""
import pickle, glob
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('neighbour_mover_v1.py').read().split("rec = pickle.load(open('/Users")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
rows = []
for f in sorted(glob.glob('crosser_equality_v1_part*.pkl')): rows += pickle.load(open(f, 'rb'))
rows.sort(); c = Counter(); shown = 0
for idx, R0, closers, cls, att in rows:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E)
    st = rs.index(path[-1]) + 1
    c[('last setter class', cls.get(st, 'reading 1'))] += 1
    Ns = [k for k in cls if cls[k] == 'N']
    for k1 in Ns:
        c[('N reading is the last setter', k1 == st)] += 1
        if k1 != st:
            k = k1 - 1; six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
            ws = windows(six, E, T1); n = next(i for i, (a, b, o) in enumerate(ws) if a <= T <= b); a, b, o = ws[n]
            hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
            A = [(l, h) for l, h, m in passes(a, b, lo, hi)]
            for jj in range(n): A = passes_in(ws[jj][0], ws[jj][1], A)
            l, h = A[0]; v = (l + h) / 2; nw = sorted(six + [v])
            Tn, pn = cascade(nw, E)
            c[('N not the last setter', 'moved last setter is the moved reading', nw.index(pn[-1]) == k)] += 1
            c[('N not the last setter', 'landing at the actual T is cut by the moved reading', blocked(v, T))] += 1
            if shown < 3:
                shown += 1
                print('N not the last setter: E340 index', idx, '| N reading', k1, '| last setter', st, '| actual R*', float(8 * T), '| moved R*', float(8 * Tn), '| moved reading in the way at the actual T:', blocked(v, T), '| moved last setter rank', nw.index(pn[-1]) + 1)
    if Ns: c[('crossers with N', 'last setter is N', cls.get(st) == 'N')] += 1
for kk, val in sorted(c.items(), key=str): print(val, '|', kk)
