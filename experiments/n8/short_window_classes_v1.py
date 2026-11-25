"""E943's not-understood members through the cascade (2026-11-25).  Exact Fractions.
Replays short_window_v1 exactly (same seed per part, same draws) and, for the members it left not understood:
  class N (726): some draw kept the path, the window did not grow by a factor > 10 (a point window, L0 = 0, counts as grown when any kept draw gives it positive length, as in short_window_v1);
  class Z (1,525): no draw kept the path;
records the window [a, b] (exit of six-reading x lap j, entry of six-reading y lap j'), its length L0, the ratio L0/a
(the jitter moves a by at most a*10^-7 relative), and a TARGETED move: x alone raised by a relative 10^-s, or y alone
lowered by a relative 10^-s (s = 7..14), each of which lengthens the window; kept only if the path (setter ranks and
laps) is unchanged.  For a move that changes the path, the first position at which the path differs and the reading
set there.  The cascade decides every path; the draws are seeded and steer which arrangements are tried.
"""
import pickle, random, sys
from fractions import Fraction as Fr
from math import floor
from collections import Counter
exec(open('short_window_v1.py').read().split("rec = pickle.load(open('/Users")[0])

def first_diff(s0, s1):
    for q in range(min(len(s0), len(s1))):
        if s0[q] != s1[q]: return q, s0[q], s1[q]
    return min(len(s0), len(s1)), None, None

rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
step = int(sys.argv[1]); off = int(sys.argv[2]); random.seed(off)
c = Counter(); shown = set(); out = []
for idx in range(off, len(rec), step):
    r = rec[idx]
    rs = sorted(Fr(x) for x in r[1]); six = rs[:6]
    Bk, n = bmove(six, rs[5], None)
    if Bk != 'skipped': continue
    ws = windows(six, E, T1)
    i = min(range(n + 1), key=lambda q: ws[q][1] - ws[q][0]); a, b, o = ws[i]
    ex, en = edges(six, a, b)
    if not ex or not en: continue
    (xi, j), (yi, jp) = ex[0], en[0]
    T0, sig0 = path_sig(rs); L0 = b - a; Lmax = L0; kept = 0; keptS = []
    for d in range(24):
        s = random.choice([7, 8, 9, 10])
        new = [rs[0]] + [x * (1 + Fr(random.randint(-1000, 1000), 1000 * 10 ** s)) for x in rs[1:]]
        if sorted(new) != new: continue
        T1n, sig1 = path_sig(new)
        if sig1 != sig0: continue
        kept += 1; keptS.append(s)
        x, y = new[[k for k in range(7) if k != 6][xi]], new[[k for k in range(7) if k != 6][yi]]
        Ln = Fr(8 * jp - 1, 8) / y - Fr(8 * j + 1, 8) / x
        if Ln > Lmax: Lmax = Ln
    if kept and Lmax > 10 * L0: cls = 'G'
    elif kept: cls = 'N'
    else: cls = 'Z'
    c[('class', cls)] += 1
    if cls == 'G': continue
    # targeted moves: raise x (index xi in six = index xi in rs, since six = rs[:6]) or lower y
    best = None; why = Counter()
    for which, q, sign in (('raise x', xi, 1), ('lower y', yi, -1)):
        if q == 0: why[(which, 'reading 1 is d_min, not moved')] += 1; continue
        for s in range(7, 15):
            new = list(rs); new[q] = rs[q] * (1 + sign * Fr(1, 10 ** s))
            if sorted(new) != new: why[(which, 'order changes')] += 1; continue
            T1n, sig1 = path_sig(new)
            Ln = Fr(8 * jp - 1, 8) / new[yi] - Fr(8 * j + 1, 8) / new[xi]
            if sig1 == sig0:
                f = Ln / L0 if L0 else (Fr(10) ** 40 if Ln > 0 else Fr(1))
                if best is None or f > best[0]: best = (f, which, s, Ln)
            else:
                p, e0, e1 = first_diff(sig0, sig1)
                why[(which, 'path changes')] += 1
    c[(cls, 'targeted move keeps the path' if best else 'no targeted move keeps the path')] += 1
    if best:
        c[(cls, 'targeted growth > 10' if best[0] > 10 else 'targeted growth <= 10')] += 1
        c[(cls, 'targeted length >= 10^-9' if best[3] >= Fr(1, 10 ** 9) else 'targeted length < 10^-9')] += 1
    c[(cls, 'L0 = 0 (point window)' if L0 == 0 else 'L0 > 0')] += 1
    c[(cls, 'L0/a >= 10^-8' if L0 / a >= Fr(1, 10 ** 8) else 'L0/a < 10^-8')] += 1
    c[(cls, 'x is reading %d, y is reading %d' % (xi + 1, yi + 1))] += 1
    out.append((idx, cls, xi, j, yi, jp, a, b, kept, keptS, Lmax, best, dict(why)))
    if cls not in shown:
        shown.add(cls)
        print('first member of class', cls, '| E340 index', idx, '| readings (floats, steer only)', [round(float(q), 6) for q in rs])
        print('   R*', 8 * T0, '| moves', len(sig0), '| path', sig0)
        print('   window: exit of rank', xi + 1, 'lap', j, '-> entry of rank', yi + 1, 'lap', jp, '| R', (8 * a, 8 * b))
        print('   L0', L0, '~', float(L0), '| L0/a ~', float(L0 / a), '| kept draws', kept, keptS, '| Lmax/L0 ~', (float(Lmax / L0) if L0 else 'L0 = 0'))
        print('   targeted best', None if not best else (float(best[0]), best[1], best[2], float(best[3])), '| why', dict(why))
pickle.dump(out, open('short_window_classes_v1_part%d.pkl' % off, 'wb'))
for k, val in sorted(c.items(), key=str): print(val, k)
