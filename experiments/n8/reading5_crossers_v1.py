"""E940 item 6, second exception, through the cascade (2026-11-25).  Exact Fractions.
The gate crossers of E340 (R* >= 9, 4,939) and the neighbour-held bounds B_k (neighbour_mover_v1).  For each crosser:
the cascade's last setter (the opener of the landing window: rank, lap), the reading that closes the landing window
(the first zone entered after T), B_k for k = 2..7, and the set of k attaining min B_k.  Question: is the attaining
set read off the landing (opener, closer), in particular for the 24 crossers whose minimum is attained by k = 5 only.
"""
import pickle
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('neighbour_mover_v1.py').read().split("rec = pickle.load")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
c = Counter(); shown = 0
for r in rec:
    rs = sorted(Fr(x) for x in r[1]); T, path = cascade(rs, E); R = 8 * T
    if R < 9: continue
    op = rs.index(path[-1]) + 1 if path else 1
    oplap = floor(path[-1] * T + E) - 1 if path else 0
    nxt_entries = [((ceil(x * T - E)) - E) / x if (x * T - E) % 1 else None for x in rs]
    ents = [((floor(x * T + E)) + 1 - E) / x for x in rs]
    cl = min(range(7), key=lambda i: ents[i]) + 1
    B = {}
    for k in range(1, 7):
        six = rs[:k] + rs[k + 1:]
        Bk, n = bmove(six, rs[k - 1], rs[k + 1] if k < 6 else None)
        if isinstance(Bk, Fr): B[k + 1] = Bk
    m = min(B.values()); att = tuple(k for k in B if B[k] == m)
    c[('opener rank', op, 'in attaining set' if op in att else 'NOT in attaining set')] += 1
    c[('closer rank', cl, 'in attaining set' if cl in att else 'NOT in attaining set')] += 1
    c[('min B = 8 * end of the landing window', m == 8 * min(ents))] += 1
    if att == (5,):
        c[('k=5 only', 'opener', op)] += 1; c[('k=5 only', 'closer', cl)] += 1
        if shown < 2:
            shown += 1
            print('k=5-only crosser: readings', [round(float(x), 6) for x in rs], '(floats steer only)')
            print('   R* =', R, '~', round(float(R), 6), '| opener rank', op, '| closer rank', cl, '| moves', len(path))
            print('   B_k:', {k: (str(v), round(float(v), 6)) for k, v in B.items()})
for k, v in sorted(c.items(), key=str): print(v, k)
