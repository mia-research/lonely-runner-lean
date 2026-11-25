"""E947 v2: island width and phase 2 from 9, every crosser (2026-11-25).  Exact Fractions.
v1's island-end test is true by definition (a position fails the gate iff its path differs before state 9, E340), and
its "lands in W_k" test should be "lands no later than end(W_k)"; both are replaced.
Island of reading k = the run of consecutive gate-crossing samples (as v1: 150 equal points, the actual position, the
pass-interval midpoints of six-windows up to the one after W_k) containing the actual position; its ends are bisected on
the gate predicate (R* >= 9, 90 halvings).  Recorded: the island's relative width (hi - lo)/r_k (exact), the latest
sampled island landing against 8 end(W_k), and the class (crosser_equality_v1).  Inside the island phase 1 reaches the
state 9 exactly (E340), so the landing there is the cascade from R = 9 with reading k at that position.
Per crosser: is the non-closer reading with the narrowest island one that attains min B_k (class L, P, X)?
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
def gate(rs): return 8 * cascade(rs, E)[0] >= 9
def edge(f, a, b):  # f(a) True, f(b) False
    for _ in range(90):
        m = (a + b) / 2
        if f(m): a = m
        else: b = m
    return a
step = int(sys.argv[1]); off = int(sys.argv[2]); c = Counter(); out = []
bins = [Fr(1, 10 ** e) for e in (2, 3, 4, 5, 6)]
def wbin(w):
    for e, b in zip((2, 3, 4, 5, 6), bins):
        if w >= b: return '>= 10^-%d' % e
    return '< 10^-6'
for idx, R0, closers, cls, att in rows[off::step]:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, _ = cascade(rs, E)
    rk = {}
    for k in range(1, 7):
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]; hi = rs[k + 1] if k < 6 else 2 * rs[6]
        ws = windows(six, E, T1); nW = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); Wb = ws[nW][1]
        pts = [lo + (hi - lo) * Fr(i, 150) for i in range(1, 150)] + [rs[k]]
        for x, y, z in ws[:nW + 2]:
            P = passes(x, y, lo, hi, limit=5000)
            if P: pts += [(l + h) / 2 for l, h, m in P]
        pts = sorted(set(p for p in pts if lo < p < hi))
        Ts = {v: cascade(sorted(six + [v]), E)[0] for v in pts}
        ia = pts.index(rs[k]); i0 = ia
        while i0 > 0 and 8 * Ts[pts[i0 - 1]] >= 9: i0 -= 1
        i1 = ia
        while i1 < len(pts) - 1 and 8 * Ts[pts[i1 + 1]] >= 9: i1 += 1
        g = lambda v, six=six: gate(sorted(six + [v]))
        left = edge(g, pts[i0], pts[i0 - 1]) if i0 > 0 else lo
        right = edge(g, pts[i1], pts[i1 + 1]) if i1 < len(pts) - 1 else hi
        w = (right - left) / rs[k]
        late = max(Ts[pts[i]] for i in range(i0, i1 + 1)) > Wb
        cl = cls[k + 1]
        c[('class', cl, 'island relative width', wbin(w))] += 1
        c[('class', cl, 'some island sample lands after end(W_k)', late)] += 1
        rk[k + 1] = (w, cl, late)
    nc = {k: v for k, v in rk.items() if v[1] != 'C'}
    kn = min(nc, key=lambda k: nc[k][0])
    c[('crosser', 'narrowest-island non-closer reading attains', nc[kn][1] in 'LPX')] += 1
    c[('crosser', 'narrowest-island non-closer reading', kn, nc[kn][1])] += 1
    out.append((idx, rk))
pickle.dump(out, open('path_islands_v2_part%d.pkl' % off, 'wb'))
for kk, val in sorted(c.items(), key=str): print(val, '|', kk)
