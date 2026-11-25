"""E938 item 5, test v1 (2026-11-25): are the high landings (R* >= 11) E340's gate mechanism?  Exact Fractions.
E340's gate, in the split (E933): in a crosser (R* >= 9) F passes every S window inside d_min's first window
[1/(8d), 7/(8d)].  Recorded for every E340 crosser (d_min = 1 there):
  |F|; R*; the S windows inside d's first window; for each, whether F passes it in one move and with which F reading
  and lap k (E930: f in ((8k-1)/(8a), (8k+1)/(8b))); the same for d's second window [9/(8d), 15/(8d)] up to T;
  for W_1 = [1/(8d), 7/(8 max S)], the lap k1 of a one-move pass and whether f/d lies in ((8k1-1), (8k1+1) max S/(7d)).
Grouped by R* >= 11 (the 92 of E938) and 9 <= R* < 11.
"""
import pickle
from fractions import Fraction as Fr
from math import floor
from collections import Counter
exec(open('wall_window_index_v5.py').read().split('tab = Counter(); ex = {}')[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
c = Counter(); ex = {}
def note(k, e=None):
    c[k] += 1
    if e is not None and k not in ex: ex[k] = e
for r in rec:
    rs = sorted(Fr(x) for x in r[1]); d = rs[0]; t0 = E / d
    T, _ = cascade(rs, t0); R = 8 * d * T
    if R < 9: continue
    g = 'R*>=11' if R >= 11 else '9<=R*<11'
    S = [x for x in rs if x <= 7 * d]; F = [x for x in rs if x > 7 * d]
    note((g, 'members'))
    note((g, '|F| = %d' % len(F)))
    ws = windows(S, t0, T + 1)
    first = [w for w in ws if w[1] <= 7 / (8 * d)]
    second = [w for w in ws if w[0] >= 9 / (8 * d) and w[1] < T]
    note((g, 'windows inside first d-window: %d' % len(first)))
    allone = True; laps = []
    for (a, b, o) in first:
        mv, passed, st, _ = f_run(F, a, b)
        if not passed: note((g, 'a first-window S window NOT passed'), [str(x) for x in rs])
        if mv != 1: allone = False
        laps.append(st[0][1] if st else None)
    note((g, 'every first-window pass in one move' if allone else 'some first-window pass in 2+ moves'))
    if len(F) == 1:
        f = F[0]
        note((g, '|F|=1: laps of f across first-window passes ' + '-'.join(map(str, laps))))
        a, b, o = first[0]; k1 = laps[0]
        ok = (8 * k1 - 1) * d < f < Fr(8 * k1 + 1, 7) * max(S)
        note((g, '|F|=1: W_1 one-move cell (8k1-1)d < f < (8k1+1) maxS/7 holds' if ok else '|F|=1: cell fails'))
        note((g, '|F|=1: k1 = %d' % k1))
        allone2 = True
        for (a2, b2, o2) in second:
            mv, passed, st, _ = f_run(F, a2, b2)
            if mv != 1 or not passed: allone2 = False
        note((g, '|F|=1: every second-window pass before T in one move' if allone2 else '|F|=1: other'))
for k, v in sorted(c.items(), key=str): print(v, k)
for k, e in ex.items(): print('example', k, e)
