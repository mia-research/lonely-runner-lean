"""The R* bound with one fast reading, test v2 (2026-11-25): v1 plus an exact upper bound per S over every f.
Walk S's windows in order from t0 = 1/8 (d = 1), intersecting the f-sets A as in v1.  If A becomes empty at the
window W = [a, b], no single f passes W, so for every f the landing is at or before b: B(S) = 8b bounds R* for all
f in (7, 10^4) [P, from E929 item 1 and E930 item 1].  Reported: the largest B(S), the S attaining it, its windows
and the f-set just before W; and the count of S whose bound lies in d's first arc, second arc, or later.
"""
import itertools, pickle, sys
from fractions import Fraction as Fr
exec(open('one_fast_reach_v1.py').read().split('cnt = dict(')[0])
def bound(S):
    ws = windows(S, E, Fr(31, 8)); A = [(Fr(7), Fr(10) ** 4)]
    for n, (a, b, o) in enumerate(ws):
        B = inter(A, allowed(a, b, max(h for l, h in A)))
        if not B: return 8 * b, n, A, ws
        A = B
    return None, None, A, ws
from collections import Counter
c = Counter(); best = (Fr(0), None)
mode = sys.argv[1]
def go(S):
    global best
    Bd, n, A, ws = bound(S)
    if Bd is None: c['no bound below 31'] += 1; return
    c['bound in arc 0 (<= 7)' if Bd <= 7 else ('bound in arc 1 (9..15)' if Bd <= 15 else 'bound later')] += 1
    if Bd > best[0]: best = (Bd, S, n, A, ws)
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
Bd, S, n, A, ws = best
print('largest bound B(S) =', Bd, '=', round(float(Bd), 6), '(float steers only) | S =', [str(x) for x in S])
print('   blocking window index', n + 1, '=', (str(ws[n][0]), str(ws[n][1])), '| f-set before it:', [(str(l), str(h)) for l, h in A][:4])
