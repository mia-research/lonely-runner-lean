"""E946: each gate crosser's neighbour families through the cascade (2026-11-25).  Exact Fractions.
For each of E340's 4,939 crossers and each reading k = 2..7 moved across (r_{k-1}, r_{k+1}) (k = 7: (r_6, 2 r_7)) with
the other six frozen: the cascade at 150 equally spaced exact points, the actual position, and the midpoint of every
interval passing each six-window up to the one after W_k on its own (narrow cells; PARTIAL: cells between samples are
missed).  Recorded: which sampled positions cross the gate (R* >= 9, E340), whether they are all in the actual
position's path cell (same path), the largest sampled landing, and whether B_k = 8 end of the six-window holding it.
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
def sig(rs):
    T, path = cascade(rs, E); t = E; s = []
    for p in path:
        lap = floor(p * t + E); s.append((rs.index(p), lap)); t = (lap + E) / p
    return T, tuple(s)
step = int(sys.argv[1]); off = int(sys.argv[2]); c = Counter(); out = []
for idx, R0, closers, cls, att in rows[off::step]:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, s0 = sig(rs)
    fam = {}
    for k in range(1, 7):
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]; hi = rs[k + 1] if k < 6 else 2 * rs[6]
        ws = windows(six, E, T1); nW = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y)
        pts = [lo + (hi - lo) * Fr(i, 150) for i in range(1, 150)] + [rs[k]]
        for x, y, z in ws[:nW + 2]:
            P = passes(x, y, lo, hi, limit=5000)
            if P: pts += [(l + h) / 2 for l, h, m in P]
        pts = sorted(set(p for p in pts if lo < p < hi))
        res = [(v,) + sig(sorted(six + [v])) for v in pts]
        cross = [(v, Tn, sn) for v, Tn, sn in res if 8 * Tn >= 9]
        Lmax = max(8 * Tn for v, Tn, sn in res)
        wend = next(8 * y for x, y, z in ws if x <= Lmax / 8 <= y)
        Bk, n = bmove(six, lo, rs[k + 1] if k < 6 else None)
        only = all(sn == s0 for v, Tn, sn in cross)
        inwin = all(ws[nW][0] <= Tn <= ws[nW][1] for v, Tn, sn in cross)
        fam[k + 1] = (only, inwin, Lmax == 8 * T, Bk == wend, cls[k + 1])
        c[('B_k = 8 end of the six-window holding the largest sampled landing', Bk == wend)] += 1
        c[('class', cls[k + 1], 'only the actual cell crosses' if only else 'other cells cross')] += 1
        c[('class', cls[k + 1], 'every crossing sample lands in W_k' if inwin else 'some crossing sample lands outside W_k')] += 1
        c[('class', cls[k + 1], 'actual R* is the largest sampled landing' if Lmax == 8 * T else 'a larger landing in the segment')] += 1
    c[('crosser', 'some non-closer reading: only the actual cell crosses', any(fam[k][0] and fam[k][4] != 'C' for k in fam))] += 1
    c[('crosser', 'some non-closer reading: every crossing sample lands in W_k', any(fam[k][1] and fam[k][4] != 'C' for k in fam))] += 1
    out.append((idx, fam))
pickle.dump(out, open('crosser_family_v1_part%d.pkl' % off, 'wb'))
for kk, val in sorted(c.items(), key=str): print(val, '|', kk)
