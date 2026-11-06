# E822: chain / bound2 by chain length, 53 cores and others (exact).
import pickle
from fractions import Fraction as F
res = pickle.load(open('chain_bound2_v1.pkl', 'rb'))
in53 = {tuple(map(int, l.split(','))) for l in open('core_cover_cores.txt') if l.strip()}
def med(q): q = sorted(q); return q[len(q) // 2]
for lo, hi in [(2, 2), (3, 4), (5, 7), (8, 12), (13, 99)]:
    for tag, f in [('53', True), ('others', False)]:
        sel = [r for r in res if lo <= r[1] <= hi and (r[0] in in53) == f]
        if sel: print('chain length', lo, '-', hi, tag, len(sel), 'chain/bound2 min', min(F(r[1], r[2]) for r in sel), 'median', med([F(r[1], r[2]) for r in sel]), 'max', max(F(r[1], r[2]) for r in sel))
