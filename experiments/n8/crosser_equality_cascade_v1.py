"""E945: the positions behind E941's equality, through the cascade (2026-11-25).  Exact Fractions.
For each gate crosser (crosser_equality_v1 pickles) and each reading k of class X or N, the intervals of k's segment
(r_{k-1}, r_{k+1}) that pass W_k on their own.  At the midpoint of each (up to 20 per k), the cascade is run on the
arrangement with k moved there (all other readings frozen; order kept, so it is a position between neighbours):
  class X: where it lands (before W_k: in the first six-window that position does not pass; which window);
  class N: where it lands for the positions that also pass every earlier six-window (after end(W_k)).
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
step = int(sys.argv[1]); off = int(sys.argv[2])
c = Counter(); shown = set()
for idx, R0, closers, cls, att in rows[off::step]:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, _ = cascade(rs, E)
    for k1, cl in cls.items():
        if cl not in 'XN': continue
        k = k1 - 1; six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1); n = next(i for i, (a, b, o) in enumerate(ws) if a <= T <= b); a, b, o = ws[n]
        hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
        P = [(l, h) for l, h, m in passes(a, b, lo, hi)]
        for l, h in P[:20]:
            v = (l + h) / 2; nw = sorted(six + [v])
            Tn, _ = cascade(nw, E)
            # first six-window the position does not pass (none before W_k means it passes all earlier ones)
            fail = next((jj for jj in range(n) if not passes_in(ws[jj][0], ws[jj][1], [(v - Fr(1, 10 ** 40), v + Fr(1, 10 ** 40))])), None)
            where = 'lands before W_k' if Tn < a else ('lands in W_k' if Tn <= b else 'lands after W_k')
            c[(cl, where)] += 1
            if fail is not None:
                c[(cl, 'first earlier window failed', 'window 1' if fail == 0 else ('the one before W_k' if fail == n - 1 else 'other'))] += 1
                fw = ws[fail]
                c[(cl, 'lands in the first window failed', fw[0] <= Tn <= fw[1])] += 1
            else:
                c[(cl, 'passes every earlier window')] += 1
            if (cl, where) not in shown:
                shown.add((cl, where))
                print('first', cl, where, '| E340 index', idx, '| k', k1, '| position (float, steer only) %.6f' % float(v), '| R* member', 8 * T, '| R* moved', 8 * Tn, '~ %.6f' % float(8 * Tn), '| W_k R', (float(8 * a), float(8 * b)), '| first earlier window failed', None if fail is None else fail + 1)
for kk, val in sorted(c.items(), key=str): print(val, '|', kk)
