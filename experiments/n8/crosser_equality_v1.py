"""E941's equality min_k B_k = 8 * end of the landing window, through the cascade (2026-11-25).  Exact Fractions.
The 4,939 gate crossers of E340 (R* >= 9).  For each reading k = 2..7 held between its neighbours (lo, hi) = (r_{k-1},
r_{k+1}) (k = 7: hi open) with the other six frozen, W_k = the six's clear window holding T.  By E941 [P],
B_k >= 8 end(W_k) >= 8 end(landing window), and B_k = 8 end(landing) iff end(W_k) = end(landing) (k is not the
closer) and no position of k that passes every earlier six-window passes W_k.  Each k is sorted by the first reason
that holds:
  C  k is the closer: end(W_k) > end(landing);
  L  length: |W_k| >= 1/(4 lo), so no zone of any position of k (length 1/(4 r) < 1/(4 lo)) contains W_k;
  P  W_k's own pass set in (lo, hi) is empty, though length allows it (the laps' positions miss the segment);
  X  W_k's pass set in (lo, hi) is non-empty, but no position in it passes every earlier six-window;
  N  some position passes every earlier window and W_k: B_k > 8 end.
k attains min B_k iff its class is L, P or X.  Checked against B_k from neighbour_mover_v1's bmove (exact).
"""
import pickle, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('neighbour_mover_v1.py').read().split("rec = pickle.load(open('/Users")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
step = int(sys.argv[1]); off = int(sys.argv[2])
c = Counter(); shown = False; out = []
for idx in range(off, len(rec), step):
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); R = 8 * T
    if R < 9: continue
    ents = [(floor(x * T + E) + 1 - E) / x for x in rs]; end = min(ents)
    closers = [i + 1 for i in range(7) if ents[i] == end]
    cls = {}; B = {}
    for k in range(1, 7):
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1)
        n = next(i for i, (a, b, o) in enumerate(ws) if a <= T <= b); a, b, o = ws[n]
        hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1 if b > a else Fr(10) ** 4
        if b > end: cl = 'C'
        elif b - a >= Fr(1, 4) / lo: cl = 'L'
        else:
            P = [(l, h) for l, h, m in passes(a, b, lo, hi)]
            if not P: cl = 'P'
            else:
                A = P
                for jj in range(n):
                    if not A: break
                    A = passes_in(ws[jj][0], ws[jj][1], A)
                cl = 'X' if not A else 'N'
        cls[k + 1] = cl
        Bk, nn = bmove(six, lo, rs[k + 1] if k < 6 else None)
        if isinstance(Bk, Fr): B[k + 1] = Bk
    m = min(B.values()); att = tuple(k for k in B if B[k] == m)
    pred = tuple(k for k in cls if cls[k] in 'LPX')
    c[('members',)] += 1
    c[('min B = 8 end', m == 8 * end)] += 1
    c[('attaining set = classes L, P, X', att == pred)] += 1
    for k, cl in cls.items(): c[('class of k', k, cl)] += 1
    c[('classes present in the attaining set', ''.join(sorted(set(cls[k] for k in pred))))] += 1
    c[('slowest attaining k', min(pred) if pred else None, cls[min(pred)] if pred else None)] += 1
    c[('k = 2 attains', cls[2] in 'LPX', cls[2])] += 1
    out.append((idx, R, closers, cls, att))
    if not shown:
        shown = True
        print('first crosser: E340 index', idx, '| readings (floats, steer only)', [round(float(q), 6) for q in rs])
        print('   R*', R, '| moves', len(path), '| landing window R', (R, 8 * end), '| closer rank', closers, '| opener rank', rs.index(path[-1]) + 1)
        print('   classes', cls, '| B_k', {k: str(v) for k, v in B.items()}, '| attaining', att)
pickle.dump(out, open('crosser_equality_v1_part%d.pkl' % off, 'wb'))
for k, val in sorted(c.items(), key=str): print(val, '|', k)
