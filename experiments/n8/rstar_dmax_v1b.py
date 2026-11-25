"""rstar_dmax_v1 (a), rule 22 on the 460 shifts that lower R*: at the new landing T1 < T, check exactly that
(i) every reading other than the shifted one is clear, (ii) the old reading f was in the way (sole blocker, E754
`displaced_earlier`), (iii) where T1 falls: R1 = 8 d T1 in d's first window [1, 7] or later; and the max reading of
the 92 members.  Exact Fractions."""
import pickle
from fractions import Fraction as Fr
from math import floor
from collections import Counter
exec(open('wall_window_index_v5.py').read().split('def windows')[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
c = Counter(); mx = Fr(0); nfast = Counter()
for r in rec:
    rs = sorted(Fr(x) for x in r[1]); d = rs[0]; T, _ = cascade(rs, E / d)
    if 8 * d * T < 11: continue
    mx = max(mx, rs[-1] / d); nfast[sum(1 for x in rs if x > 7 * d)] += 1
    for j in range(1, 6):
        for idx, f in enumerate(rs):
            if f <= 7 * d: continue
            new = list(rs); new[idx] = f + Fr(j) / T
            if len(set(new)) < 7: continue
            T1, _ = cascade(sorted(new), E / d)
            others = [x for k, x in enumerate(rs) if k != idx]
            c['T1 < T'] += T1 < T
            c['others clear at T1'] += all(not blocked(x, T1) for x in others)
            c['old f in the way at T1'] += blocked(f, T1)
            R1 = 8 * d * T1
            c['R1 in [1,7]' if R1 <= 7 else ('R1 in [9,15]' if 9 <= R1 <= 15 else 'R1 other')] += 1
            c['cases'] += 1
for k, v in c.items(): print(v, k)
print('largest reading / d_min among the 92 members:', mx, '=', round(float(mx), 4), '(float steers only)')
print('number of readings above 7 d_min among the 92:', dict(nfast))
