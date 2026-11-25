"""Removing the f cap in v2's bound (2026-11-25).  f passes the S window [a, b] only if [a, b] lies inside one zone of f
where f is in the way, of length 1/(4f) (E930 item 1), so f < 1/(4(b - a)).  If some window at or before v2's blocking
window W has length L > 1/(4 * 10^4), no f >= 10^4 passes it, and v2's bound B(S) then holds for every f > 7.
Reported per population: how many S have such a window (cap removed) and how many do not.
"""
import itertools, pickle, sys
from fractions import Fraction as Fr
from collections import Counter
exec(open('one_fast_reach_v2.py').read().split('from collections import Counter')[0])
cap = Fr(1, 4 * 10 ** 4); c = Counter(); mode = sys.argv[1]
def go(S):
    Bd, n, A, ws = bound(S)
    if Bd is None: c['no bound'] += 1; return
    L = max(b - a for a, b, o in ws[:n + 1])
    c['cap removed (a window longer than 1/40000)' if L > cap else 'cap NOT removed'] += 1
if mode == 'grid':
    vals = [Fr(i, 6) for i in range(7, 43)]
    for cc in itertools.combinations(vals, 5): go([Fr(1)] + list(cc))
else:
    rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
    seen = set()
    for r in rec:
        rs = sorted(Fr(x) for x in r[1]); S = [x for x in rs if x <= 7]
        if len(S) != 6 or tuple(S) in seen: continue
        seen.add(tuple(S)); go(S)
print(mode, dict(c))
