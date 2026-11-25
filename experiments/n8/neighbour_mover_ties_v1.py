"""E940 rule-22 item (2026-11-25): the members of E340 with min_k B_k = R* exactly (neighbour_mover_v1).  Exact.
For each: the blocking window W = [a, b] of the attaining mover's frozen six has 8b = R*, so the cascade lands at W's
right end.  Reported: which frozen reading's zone opens at b (b = (8j - 1)/(8 r)), and which reading's zone closes at
b (b = (8j + 1)/(8 r)), i.e. whether the landing is an exit = entry coincidence of two zones (E373).
"""
import pickle
from fractions import Fraction as Fr
from math import floor
exec(open('neighbour_mover_v1.py').read().split("rec = pickle.load")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
found = 0
for r in rec:
    rs = sorted(Fr(x) for x in r[1]); T, _ = cascade(rs, E); R = 8 * T
    if R > 7: continue
    Bs = {}
    for k in range(1, 7):
        six = rs[:k] + rs[k + 1:]; Bk, n = bmove(six, rs[k - 1], rs[k + 1] if k < 6 else None)
        if isinstance(Bk, Fr): Bs[k + 1] = Bk
    if not Bs or min(Bs.values()) != R: continue
    found += 1
    opens = [(i + 1, int(8 * rs[i] * T + 1) // 8) for i in range(7) if (8 * rs[i] * T + 1) % 8 == 0]
    closes = [(i + 1, int(8 * rs[i] * T - 1) // 8) for i in range(7) if (8 * rs[i] * T - 1) % 8 == 0]
    print('R* =', R, '| zones entered at T (rank, lap):', opens, '| zones exited at T (rank, lap):', closes)
print('members with min B = R*:', found)
