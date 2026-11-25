"""Neighbour ratios against the landing, E340's 110,081 members (2026-11-25).  Exact Fractions.
For each member (readings r_1 < ... < r_7, d = r_1 = 1): the largest neighbour ratio r_{k+1}/r_k and where it sits (k),
the landing R*, and whether the member's six-slowest set was skipped by one_mover_bound_v1 (its longest window's pass
set has more than 2*10^5 laps).  Reported: for R* <= 7 and R* >= 9, the largest neighbour ratio (exact), how many
members have a ratio above 7 and at which k; and for the skipped sixes, r_2 against 7 and their landings.
"""
import pickle
from fractions import Fraction as Fr
from collections import Counter
exec(open('one_mover_bound_v1.py').read().split("if __name__")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
c = Counter(); mx = {}; memo = {}
for r in rec:
    rs = sorted(Fr(x) for x in r[1]); T, _ = cascade(rs, E); R = 8 * T
    side = 'R*<=7' if R <= 7 else 'R*>=9'
    rat = [(rs[k + 1] / rs[k], k + 1) for k in range(6)]; q, k = max(rat)
    if side not in mx or q > mx[side][0]: mx[side] = (q, k, rs)
    if q > 7: c[(side, 'some neighbour ratio > 7, at k = %d' % k)] += 1
    six = tuple(rs[:6])
    if six not in memo: memo[six] = bstar(list(six))[0] == 'skipped'
    if memo[six]:
        c[('skipped six', side)] += 1
        c[('skipped six', 'r_2 > 7' if rs[1] > 7 else 'r_2 <= 7')] += 1
for k, v in sorted(c.items(), key=str): print(v, k)
for side, (q, k, rs) in sorted(mx.items()):
    print(side, ': largest neighbour ratio', q, '~', round(float(q), 6), '(float steers only) at k =', k)
