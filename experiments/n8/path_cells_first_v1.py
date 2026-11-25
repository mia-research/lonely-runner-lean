"""E947: the first gate crosser's neighbour families as path cells, exact breakpoints (2026-11-25).  Exact Fractions.
E340 index 44824 (the first crosser of crosser_equality_v1).  Each reading k = 2..7 moved across (r_{k-1}, r_{k+1})
(k = 7: (r_6, 2 r_7)), the other six frozen.  The cascade at 600 equally spaced points plus the actual position and the
midpoints of the pass intervals of the six-windows up to the one after W_k; each change of path between neighbouring
samples is bisected (90 halvings) to a breakpoint.  For each cell: its interval, the path length, the landing R*, and
whether it crosses the gate (R* >= 9).  For each breakpoint: the first move at which the two paths differ, the state's R
there, the readings in the way on each side, and the setter on each side.  The gate island: the run of gate-crossing
cells containing the actual position, and the breakpoints that bound it.
"""
import pickle, sys
from fractions import Fraction as Fr
from math import floor, ceil
exec(open('neighbour_mover_v1.py').read().split("rec = pickle.load(open('/Users")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
def run(rs):
    T, path = cascade(rs, E); t = E; s = []; st = []
    for p in path:
        lap = floor(p * t + E); st.append((t, tuple(q + 1 for q in range(7) if blocked(rs[q], t)))); s.append((rs.index(p) + 1, lap)); t = (lap + E) / p
    return T, tuple(s), st
def cells_of(rs, k, N=600, extra=True):
    six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]; hi = rs[k + 1] if k < 6 else 2 * rs[6]
    T, _, _ = run(rs)
    ws = windows(six, E, T1); nW = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y)
    pts = [lo + (hi - lo) * Fr(i, N) for i in range(1, N)] + [rs[k]]
    if extra:
        for x, y, z in ws[:nW + 2]:
            P = passes(x, y, lo, hi, limit=5000)
            if P: pts += [(l + h) / 2 for l, h, m in P]
    pts = sorted(set(p for p in pts if lo < p < hi))
    at = lambda v: run(sorted(six + [v]))
    res = [(v,) + at(v) for v in pts]
    cells = []; bps = []
    cur = [res[0][0], res[0][0], res[0][1], res[0][2]]
    for (v0, T0, s0, st0), (v1, T1_, s1, st1) in zip(res, res[1:]):
        if s1 == cur[3]: cur[1] = v1; continue
        a, b = v0, v1
        for _ in range(90):
            m = (a + b) / 2
            if at(m)[1] == s0: a = m
            else: b = m
        La, Lb = at(a), at(b)
        p = next((u for u in range(min(len(La[1]), len(Lb[1]))) if La[1][u] != Lb[1][u]), min(len(La[1]), len(Lb[1])))
        sa = La[2][p] if p < len(La[2]) else (La[0], ()); sb = Lb[2][p] if p < len(Lb[2]) else (Lb[0], ())
        bps.append(((a + b) / 2, p, 8 * sa[0], sa[1], sb[1], La[1][p] if p < len(La[1]) else None, Lb[1][p] if p < len(Lb[1]) else None))
        cells.append(cur); cur = [v1, v1, T1_, s1]
    cells.append(cur)
    return lo, hi, cells, bps, ws, nW
if __name__ == '__main__':
    idx = 44824
    rs = sorted(Fr(x) for x in rec[idx][1]); T, s0, _ = run(rs)
    print('E340 index', idx, '| readings (floats, steer only)', [round(float(q), 6) for q in rs], '| R*', 8 * T, '| moves', len(s0))
    for k in range(1, 7):
        lo, hi, cells, bps, ws, nW = cells_of(rs, k)
        ia = next(i for i, c in enumerate(cells) if c[0] <= rs[k] <= c[1])
        print('\nk = %d | segment (%.6f, %.6f) | actual %.6f | cells %d | W_k R (%.6f, %.6f)' % (k + 1, float(lo), float(hi), float(rs[k]), len(cells), float(8 * ws[nW][0]), float(8 * ws[nW][1])))
        for i, c in enumerate(cells):
            mark = ' <- actual' if i == ia else ''
            print('   cell %2d [%.9f, %.9f] | moves %2d | R* %.6f%s%s' % (i, float(c[0]), float(c[1]), len(c[3]), float(8 * c[2]), ' | crosses the gate' if 8 * c[2] >= 9 else '', mark))
            if i < len(bps):
                bp, p, Rs, ina, inb, sa, sb = bps[i]
                print('        break at %.12f: paths differ at move %d, state R %.6f%s | in the way: %s -> %s | setter %s -> %s' % (float(bp), p, float(Rs), ' (phase 1)' if Rs < 9 else ' (phase 2)', ina, inb, sa, sb))
        lo_i = ia
        while lo_i > 0 and 8 * cells[lo_i - 1][2] >= 9: lo_i -= 1
        hi_i = ia
        while hi_i < len(cells) - 1 and 8 * cells[hi_i + 1][2] >= 9: hi_i += 1
        print('   gate island: cells %d..%d | landings %s | inside W_k: %s' % (lo_i, hi_i, [round(float(8 * cells[i][2]), 6) for i in range(lo_i, hi_i + 1)], all(ws[nW][0] <= cells[i][2] <= ws[nW][1] for i in range(lo_i, hi_i + 1))))
