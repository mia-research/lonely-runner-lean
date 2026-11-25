"""v2: as v1, accepting any ratio q with numerator and denominator below 2000 (v1 required both = +-1 mod 8, which a reduced
fraction such as 15/9 = 5/3 fails).
E949: why class X attains, in ratios (2026-11-25).  Exact Fractions.
For each gate crosser (E340) and each non-closer reading k of class X or N (E945): P = the pass intervals of W_k inside
the neighbours (lo, hi) (k = 7: hi as crosser_equality_v1), A = the positions of k that pass every earlier six-window
(intervals, from (lo, hi)).  Class X iff P and A are disjoint.  For X: the closest pair (one interval of P, one of A) and
their facing ends x_P and x_A.  Each facing end is identified as a ratio multiple of one reading: x = q r_j with q = a
ratio of two numbers each = +-1 mod 8 (numerator and denominator below 10^3), or q = 1 (a neighbour).  Recorded: whether
both facing ends are multiples of the SAME reading (then the gap is the fixed ratio q_P/q_A, independent of every other
reading), the reading's role (opener / closer / other), the side, and the ratio."""
import pickle, glob, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('island_ends_v2.py').read().split("mode = sys.argv[1]")[0])
def ident(x, rs):
    for j in range(7):
        q = x / rs[j]
        if q.numerator < 2000 and q.denominator < 2000: return j + 1, q
        if q == 1: return j + 1, q
    return None, None
step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter(); ex = []
for idx, R0, closers, cls, att in rows[off::step]:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); o = rs.index(path[-1]) + 1
    for k in range(1, 7):
        kc = cls[k + 1]
        if kc not in 'XN': continue
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1); n = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[n][0], ws[n][1]
        hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
        P = [(l, h) for l, h, m in passes(a, b, lo, hi)]
        A = [(lo, hi)]
        for jj in range(n):
            if not A: break
            A = passes_in(ws[jj][0], ws[jj][1], A)
        if kc == 'N': continue
        if not A: c[('X', 'A empty')] += 1; continue
        best = None
        for lp, hp in P:
            for la, ha in A:
                if hp <= la: d, xP, xA, side = la - hp, hp, la, 'P below A'
                elif ha <= lp: d, xP, xA, side = lp - ha, lp, ha, 'P above A'
                else: d = 0; xP = xA = None; side = 'overlap'
                if best is None or d < best[0]: best = (d, xP, xA, side)
        d, xP, xA, side = best
        if d == 0: c[('X', 'P meets A (check)')] += 1; continue
        jP, qP = ident(xP, rs); jA, qA = ident(xA, rs)
        role = lambda j: 'none' if j is None else ('opener' if j == o else ('closer' if j in closers else ('moved' if j == k + 1 else 'other')))
        same = jP is not None and jP == jA
        c[('X', side, 'P end reading', role(jP), 'A end reading', role(jA), 'same reading', same)] += 1
        if same:
            r = qP / qA
            c[('X', 'same reading: ratio', str(r))] += 1
        else:
            c[('X', 'different readings', 'P end', (jP, str(qP)), 'A end', (jA, str(qA)))] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
