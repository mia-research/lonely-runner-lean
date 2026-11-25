"""E947: gate islands of every crosser's neighbour families, through the cascade (2026-11-25).  Exact Fractions.
For each of E340's 4,939 crossers and each reading k = 2..7 moved across (r_{k-1}, r_{k+1}) (k = 7: (r_6, 2 r_7)), the
other six frozen: the cascade at 150 equally spaced points, the actual position, and the midpoints of the pass
intervals of the six-windows up to the one after W_k (PARTIAL: cells between samples are missed).  The ISLAND is the
run of consecutive gate-crossing samples (R* >= 9, E340) containing the actual position.  Each path change at the
island's two ends and inside it is bisected (90 halvings); for each, the state R at the first differing move
(phase 1 if below 9, phase 2 if 9 or above).  Recorded: island ends (phase 1 / phase 2 / segment end), the number of
phase-2 changes inside, whether every island sample lands in W_k, and the reading's class (crosser_equality_v1).
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
def run(rs):
    T, path = cascade(rs, E); t = E; s = []; st = []
    for p in path:
        lap = floor(p * t + E); st.append(t); s.append((rs.index(p), lap)); t = (lap + E) / p
    return T, tuple(s), st
def brk(at, a, b, s0):
    for _ in range(90):
        m = (a + b) / 2
        if at(m)[1] == s0: a = m
        else: b = m
    La, Lb = at(a), at(b)
    p = next((u for u in range(min(len(La[1]), len(Lb[1]))) if La[1][u] != Lb[1][u]), min(len(La[1]), len(Lb[1])))
    t = La[2][p] if p < len(La[2]) else La[0]
    return 8 * t
step = int(sys.argv[1]); off = int(sys.argv[2]); c = Counter(); out = []
for idx, R0, closers, cls, att in rows[off::step]:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, s0, _ = run(rs)
    rec_k = {}
    for k in range(1, 7):
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]; hi = rs[k + 1] if k < 6 else 2 * rs[6]
        ws = windows(six, E, T1); nW = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); Wa, Wb = ws[nW][0], ws[nW][1]
        pts = [lo + (hi - lo) * Fr(i, 150) for i in range(1, 150)] + [rs[k]]
        for x, y, z in ws[:nW + 2]:
            P = passes(x, y, lo, hi, limit=5000)
            if P: pts += [(l + h) / 2 for l, h, m in P]
        pts = sorted(set(p for p in pts if lo < p < hi))
        at = lambda v, six=six: run(sorted(six + [v]))
        res = [(v,) + at(v) for v in pts]
        ia = next(i for i, r in enumerate(res) if r[0] == rs[k])
        i0 = ia
        while i0 > 0 and 8 * res[i0 - 1][1] >= 9: i0 -= 1
        i1 = ia
        while i1 < len(res) - 1 and 8 * res[i1 + 1][1] >= 9: i1 += 1
        ends = []
        for (i, j) in ((i0 - 1, i0), (i1, i1 + 1)):
            if i < 0 or j >= len(res): ends.append('segment end'); continue
            Rb = brk(at, res[i][0], res[j][0], res[i][2])
            ends.append('phase 1' if Rb < 9 else 'phase 2')
        p2 = 0
        for i in range(i0, i1):
            if res[i][2] != res[i + 1][2]:
                Rb = brk(at, res[i][0], res[i + 1][0], res[i][2])
                if Rb >= 9: p2 += 1
        inW = all(Wa <= res[i][1] <= Wb for i in range(i0, i1 + 1))
        cl = cls[k + 1]
        c[('island ends', tuple(sorted(ends)))] += 1
        c[('class', cl, 'island ends', tuple(sorted(ends)))] += 1
        c[('class', cl, 'phase-2 changes inside the island', p2 if p2 < 4 else '4+')] += 1
        c[('class', cl, 'every island sample lands in W_k', inW)] += 1
        rec_k[k + 1] = (tuple(ends), p2, inW, cl, i1 - i0 + 1)
    c[('crosser', 'some non-closer reading: island with no phase-2 change', any(v[1] == 0 and v[3] != 'C' for v in rec_k.values()))] += 1
    c[('crosser', 'every reading: island ends are phase 1 or segment end', all(set(v[0]) <= {'phase 1', 'segment end'} for v in rec_k.values()))] += 1
    out.append((idx, rec_k))
pickle.dump(out, open('path_islands_v1_part%d.pkl' % off, 'wb'))
for kk, val in sorted(c.items(), key=str): print(val, '|', kk)
