"""E947 v3: the gate island against W_k's pass set (2026-11-25).  Exact Fractions.
For each crosser and each reading k of class X or N (crosser_equality_v1): the island [left, right] as in v2 (bisected
on the gate predicate R* >= 9), and every interval of k's segment that passes W_k on its own (E930; up to 40 per
reading).  For each such interval: whether its midpoint lies in the island, whether the cascade there crosses the gate,
and whether it passes every earlier six-window (lies in the walk's set A).  Question: does a reading escape (class N)
iff its own gate island meets W_k's pass set; are the would-pass positions outside the island exactly the ones that
do not cross the gate (land in phase 1)?
"""
import pickle, glob, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('path_islands_v2.py').read().split("step = int(sys.argv[1])")[0])
step = int(sys.argv[1]); off = int(sys.argv[2]); c = Counter()
for idx, R0, closers, cls, att in rows[off::step]:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, _ = cascade(rs, E)
    for k in range(1, 7):
        cl = cls[k + 1]
        if cl not in 'XN': continue
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]; hi = rs[k + 1] if k < 6 else 2 * rs[6]
        ws = windows(six, E, T1); nW = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[nW][0], ws[nW][1]
        pts = [lo + (hi - lo) * Fr(i, 150) for i in range(1, 150)] + [rs[k]]
        for x, y, z in ws[:nW + 2]:
            P = passes(x, y, lo, hi, limit=5000)
            if P: pts += [(l + h) / 2 for l, h, m in P]
        pts = sorted(set(p for p in pts if lo < p < hi))
        cr = {v: 8 * cascade(sorted(six + [v]), E)[0] >= 9 for v in pts}
        ia = pts.index(rs[k]); i0 = ia
        while i0 > 0 and cr[pts[i0 - 1]]: i0 -= 1
        i1 = ia
        while i1 < len(pts) - 1 and cr[pts[i1 + 1]]: i1 += 1
        g = lambda v, six=six: gate(sorted(six + [v]))
        left = edge(g, pts[i0], pts[i0 - 1]) if i0 > 0 else lo
        right = edge(g, pts[i1], pts[i1 + 1]) if i1 < len(pts) - 1 else hi
        hiP = hi if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
        PW = [(l, h) for l, h, m in passes(a, b, lo, hiP)][:40]
        meets = False
        for l, h in PW:
            v = (l + h) / 2; inI = left <= v <= right; meets = meets or (left < h and l < right)
            crs = gate(sorted(six + [v]))
            inA = all(passes_in(ws[jj][0], ws[jj][1], [(v - Fr(1, 10 ** 40), v + Fr(1, 10 ** 40))]) for jj in range(nW))
            c[(cl, 'would-pass midpoint', 'in the island' if inI else 'outside the island', 'crosses the gate' if crs else 'does not cross', 'in A' if inA else 'not in A')] += 1
        c[(cl, 'island meets the pass set of W_k', meets)] += 1
for kk, val in sorted(c.items(), key=str): print(val, '|', kk)
