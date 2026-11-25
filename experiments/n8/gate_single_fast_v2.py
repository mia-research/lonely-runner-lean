"""E939 rule-22 items (2026-11-25), exact Fractions, on E340's crossers (R* >= 9, d_min = 1).
(a) the 45 members with |F| = 1 and k1 = 2: f against 15 and 17 max S/7, and max S against 105/17;
(b) whether the 153 members with a first-arc pass of 2+ moves are exactly the 153 with |F| >= 2, and in each 2+-move
    pass whether consecutive zones of the chain overlap (the next zone opens before the current one closes) and
    whether the chain uses two or more distinct F readings.
"""
import pickle
from fractions import Fraction as Fr
from collections import Counter
exec(open('wall_window_index_v5.py').read().split('tab = Counter(); ex = {}')[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
c = Counter(); fr = []
for r in rec:
    rs = sorted(Fr(x) for x in r[1]); d = rs[0]; t0 = E / d
    T, _ = cascade(rs, t0); R = 8 * d * T
    if R < 9: continue
    S = [x for x in rs if x <= 7]; F = [x for x in rs if x > 7]
    first = [w for w in windows(S, t0, T + 1) if w[1] <= Fr(7, 8)]
    multi = False
    for (a, b, o) in first:
        mv, passed, st, _ = f_run(F, a, b)
        if mv >= 2:
            multi = True
            c['2+-move pass: distinct F readings in chain >= 2' if len(set(x[0] for x in st)) >= 2 else '2+-move pass: one F reading'] += 1
    c[('|F|>=2' if len(F) >= 2 else '|F|=1', 'multi' if multi else 'all one-move')] += 1
    if len(F) == 1:
        mv, passed, st, _ = f_run(F, *first[0][:2])
        if st[0][1] == 2:
            f = F[0]; mS = max(S)
            c['k1=2: 15 < f < 17 maxS/7'] += (15 < f < Fr(17, 7) * mS); c['k1=2: maxS > 105/17'] += (mS > Fr(105, 17)); c['k1=2 members'] += 1
            fr.append(f)
for k, v in sorted(c.items(), key=str): print(v, k)
print('k1=2: f range', min(fr), '..', max(fr), '(', round(float(min(fr)), 4), '..', round(float(max(fr)), 4), 'floats steer only)')
