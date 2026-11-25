"""E946: the first gate crosser with a class-N reading (E945), through the cascade (2026-11-25).  Exact Fractions.
For the actual arrangement and for the N reading moved to the midpoint of its first escaping interval (a position that
passes every earlier six-window and W_k), the two cascade paths side by side: each state (R), the setter (rank, lap),
the readings in the way; the step where they first differ; both landings.
"""
import pickle, glob
from fractions import Fraction as Fr
from math import floor, ceil
exec(open('neighbour_mover_v1.py').read().split("rec = pickle.load(open('/Users")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
rows = []
for f in sorted(glob.glob('crosser_equality_v1_part*.pkl')): rows += pickle.load(open(f, 'rb'))
rows.sort()
def trace(rs):
    T, path = cascade(rs, E); t = E; out = []
    for s in path:
        bl = [rs.index(r) + 1 for r in rs if blocked(r, t)]
        lap = floor(s * t + E); out.append((t, bl, (rs.index(s) + 1, lap))); t = (lap + E) / s
    out.append((t, [], None)); return T, out
for idx, R0, closers, cls, att in rows:
    Ns = [k for k in cls if cls[k] == 'N']
    if not Ns: continue
    rs = sorted(Fr(x) for x in rec[idx][1]); T, _ = cascade(rs, E)
    k1 = Ns[0]; k = k1 - 1; six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
    ws = windows(six, E, T1); n = next(i for i, (a, b, o) in enumerate(ws) if a <= T <= b); a, b, o = ws[n]
    hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
    A = [(l, h) for l, h, m in passes(a, b, lo, hi)]
    for jj in range(n): A = passes_in(ws[jj][0], ws[jj][1], A)
    l, h = A[0]; v = (l + h) / 2; nw = sorted(six + [v])
    print('E340 index', idx, '| readings (floats, steer only)', [round(float(q), 6) for q in rs], '| closer', closers, '| classes', cls)
    print('N reading', k1, 'segment', (float(lo), float(hi)), '| escaping intervals', len(A), '| first', (float(l), float(h)), '| moved to (float, steer only) %.9f' % float(v))
    print('six-windows of the frozen six (R):', [(round(float(8 * x), 6), round(float(8 * y), 6)) for x, y, z in ws[:n + 3]], '| W_k is window', n + 1)
    T0, p0 = trace(rs); T1n, p1 = trace(nw)
    print('landing: actual R*', 8 * T0, '~ %.6f' % float(8 * T0), '| moved R*', 8 * T1n, '~ %.6f' % float(8 * T1n))
    for i in range(max(len(p0), len(p1))):
        x = p0[i] if i < len(p0) else None; y = p1[i] if i < len(p1) else None
        fx = '' if x is None else 'R %.6f in the way %s move %s' % (float(8 * x[0]), x[1], x[2])
        fy = '' if y is None else 'R %.6f in the way %s move %s' % (float(8 * y[0]), y[1], y[2])
        print('  %2d | actual: %-60s | moved: %s' % (i, fx, fy))
    break
