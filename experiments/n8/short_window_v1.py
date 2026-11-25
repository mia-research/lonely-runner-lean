"""E941's short windows through the cascade (2026-11-25).  Exact Fractions.
The E340 members whose fastest-reading walk was skipped (neighbour_mover_v1, B_7 'skipped').  For each, take the
shortest window of the six slower readings among those met before the skip, [a, b]:
  (a) its ends as zone edges: a = exit of (reading x, lap j) and b = entry of (reading y, lap j'), and whether a is a
      state of the cascade's path at which the fastest reading v is the only reading in the way;
  (b) jitter (rule 12): readings 2..7 each moved by a relative 10^-s (s in 7, 8, 9, 10; 24 draws), kept only if the
      cascade's path (setter ranks and laps) is unchanged; the largest length of the same window, (8j'-1)/(8y) -
      (8j+1)/(8x), over the kept draws.
A window forced short by the path would stay short under every kept draw; one that grows was short in the member,
not in the path.
"""
import pickle, random, sys
from fractions import Fraction as Fr
from math import floor
from collections import Counter
exec(open('neighbour_mover_v1.py').read().split("rec = pickle.load")[0])

def path_sig(rs):
    T, path = cascade(rs, E); t = E; sig = []
    for s in path:
        lap = floor(s * t + E); sig.append((rs.index(s), lap)); t = (lap + E) / s
    return T, tuple(sig)

def states(rs):
    T, path = cascade(rs, E); t = E; st = [t]
    for s in path:
        lap = floor(s * t + E); t = (lap + E) / s; st.append(t)
    return st

def edges(six, a, b):
    ex = [(i, m) for i, x in enumerate(six) for m in [floor(x * a)] if (m + E) / x == a]
    en = [(i, m) for i, x in enumerate(six) for m in [floor(x * b) + 1] if (m - E) / x == b]
    return ex, en

rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
step = int(sys.argv[1]); off = int(sys.argv[2]); random.seed(off)
c = Counter(); show = off == 0
for r in rec[off::step]:
    rs = sorted(Fr(x) for x in r[1]); six = rs[:6]
    Bk, n = bmove(six, rs[5], None)
    if Bk != 'skipped': continue
    c['members'] += 1
    ws = windows(six, E, T1)
    i = min(range(n + 1), key=lambda q: ws[q][1] - ws[q][0]); a, b, o = ws[i]
    ex, en = edges(six, a, b)
    if not ex or not en: c['ends not both zone edges'] += 1; continue
    (xi, j), (yi, jp) = ex[0], en[0]
    c[('left end', 'exit of a six reading')] += 1
    st = states(rs); v = rs[6]
    isstate = a in st
    c['left end is a state of the path' if isstate else 'left end is not a state of the path'] += 1
    if isstate:
        bl = [q for q in range(7) if blocked(rs[q], a)]
        c['at that state only the fastest reading is in the way' if bl == [6] else 'other readings in the way there too'] += 1
    T0, sig0 = path_sig(rs); L0 = b - a; Lmax = L0; kept = 0
    for d in range(24):
        s = random.choice([7, 8, 9, 10])
        new = [rs[0]] + [x * (1 + Fr(random.randint(-1000, 1000), 1000 * 10 ** s)) for x in rs[1:]]
        if sorted(new) != new: continue
        T1n, sig1 = path_sig(new)
        if sig1 != sig0: continue
        kept += 1
        x, y = new[[k for k in range(7) if k != 6][xi]], new[[k for k in range(7) if k != 6][yi]]
        Ln = Fr(8 * jp - 1, 8) / y - Fr(8 * j + 1, 8) / x
        if Ln > Lmax: Lmax = Ln
    c['some jitter kept the path' if kept else 'no jitter kept the path'] += 1
    if kept:
        c['window grew under a kept jitter (by a factor > 10)' if Lmax > 10 * L0 else 'window did not grow by a factor > 10'] += 1
        c['largest length under a kept jitter >= 10^-9' if Lmax >= Fr(1, 10 ** 9) else 'largest length under a kept jitter < 10^-9'] += 1
    if show:
        show = False
        print('first member: six', [round(float(q), 6) for q in six], '| v', round(float(v), 6))
        print('   shortest window met before the skip: R', (round(float(8 * a), 6), round(float(8 * b), 6)), '| left end = exit of rank', xi + 1, 'lap', j, '| right end = entry of rank', yi + 1, 'lap', jp)
        print('   length', L0, '| left end a path state:', isstate, '| kept jitters', kept, '| largest length under them', Lmax, '~', float(Lmax))
for k, val in sorted(c.items(), key=str): print(val, k)
