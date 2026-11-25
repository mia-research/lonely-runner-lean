"""v2: the sample also holds the actual position and the midpoint of every interval of the segment that passes each
six-window up to the one after W_k on its own (narrow cells are missed by an equal grid; v1 missed the actual cell at k = 7).
E946: the neighbour family of the first class-N crosser in the cascade's own terms (2026-11-25).  Exact Fractions.
E340 index 66758.  Each reading k = 2..7 is moved across its segment (r_{k-1}, r_{k+1}) (k = 7: (r_6, 2 r_7)) with the
other six frozen.  The cascade is run at 600 equally spaced exact points; between neighbouring points with different
paths (setter ranks and laps) the change is bisected (70 halvings) to a breakpoint.  Reported per k: the number of
path cells met, the landing R* in each cell (exact), the largest landing over the segment, and B_k (neighbour_mover_v1)
against the end of the six-window that holds that largest landing.  The cascade decides every point.
"""
import pickle
from fractions import Fraction as Fr
from math import floor, ceil
exec(open('neighbour_mover_v1.py').read().split("rec = pickle.load(open('/Users")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
def sig(rs):
    T, path = cascade(rs, E); t = E; s = []
    for p in path:
        lap = floor(p * t + E); s.append((rs.index(p), lap)); t = (lap + E) / p
    return T, tuple(s)
idx = 66758
rs = sorted(Fr(x) for x in rec[idx][1]); T, _ = cascade(rs, E)
print('E340 index', idx, '| readings (floats, steer only)', [round(float(q), 6) for q in rs], '| R*', 8 * T, '~ %.6f' % float(8 * T))
for k in range(1, 7):
    six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]; hi = rs[k + 1] if k < 6 else 2 * rs[6]
    ws = windows(six, E, T1)
    Bk, n = bmove(six, lo, rs[k + 1] if k < 6 else None)
    N = 600; pts = [lo + (hi - lo) * Fr(i, N) for i in range(1, N)] + [rs[k]]
    nW = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y)
    for x, y, z in ws[:nW + 2]:
        P = passes(x, y, lo, hi, limit=5000)
        if P: pts += [(l + h) / 2 for l, h, m in P]
    pts = sorted(set(p for p in pts if lo < p < hi))
    at = lambda v: sig(sorted(six + [v]))
    vals = [(v,) + at(v) for v in pts]
    cells = [[vals[0][0], vals[0][0], vals[0][1], vals[0][2]]]
    for (v0, T0, s0), (v1, T1_, s1) in zip(vals, vals[1:]):
        if s1 == cells[-1][3]: cells[-1][1] = v1; continue
        a, b = v0, v1
        for _ in range(70):
            m = (a + b) / 2
            if at(m)[1] == s0: a = m
            else: b = m
        cells.append([v1, v1, T1_, s1])
    Ls = [8 * c[2] for c in cells]; Lmax = max(Ls)
    wend = next(8 * y for x, y, z in ws if x <= Lmax / 8 <= y)
    print('k = %d | segment (%.6f, %.6f) | actual position %.6f | path cells met %d | distinct landings %d | largest landing %s ~ %.6f | B_k %s ~ %.6f | B_k = 8 end of the six-window holding the largest landing: %s' % (
        k + 1, float(lo), float(hi), float(rs[k]), len(cells), len(set(Ls)), Lmax, float(Lmax), Bk, float(Bk), Bk == wend))
    print('      landings over the segment (in order, floats steer only):', [round(float(x), 4) for x in Ls][:40], '...' if len(Ls) > 40 else '')
