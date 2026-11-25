"""E939's intersection kind through the cascade (2026-11-25).  Exact Fractions.
E340's slow sets S (|S| = 6) whose f-set empties at W by intersection: W can be passed by some single f > 7 on its own,
but no f passes every window up to W (one_fast_reach_v3).  For each such S and each interval of f that passes W
alone (all of them up to 60 per S, inside (7, 10^4)), the cascade is run on S + {f} at the interval's midpoint.
Reported: whether the landing lies before W in every case; whether it lies in the first S window that f does not
pass (E929 item 1); the landing kind (opening of an S window / exit of f inside one); and which earlier window f fails.
"""
import pickle
from fractions import Fraction as Fr
from collections import Counter
exec(open('one_fast_reach_v2.py').read().split('from collections import Counter')[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
seen = set(); c = Counter()
for r in rec:
    rs = sorted(Fr(x) for x in r[1]); S = [x for x in rs if x <= 7]
    if len(S) != 6 or tuple(S) in seen: continue
    seen.add(tuple(S))
    Bd, n, A, ws = bound(S); a, b, o = ws[n]
    iv = allowed(a, b, Fr(10) ** 4)
    if not iv: continue
    c['intersection-kind sets'] += 1
    for l, h in iv[:60]:
        g = (l + h) / 2; T2, _ = cascade(sorted(S + [g]), E)
        c['positions tried'] += 1
        c['landing before W' if T2 < a else 'landing at or after W (FAIL)'] += 1
        fails = [i for i, (x, y, oo) in enumerate(ws[:n]) if not any(lo < g < hi for lo, hi in allowed(x, y, Fr(10) ** 4))]
        j = fails[0] if fails else None
        if j is None: c['f passes every window before W (FAIL)'] += 1; continue
        x, y, oo = ws[j]
        c['landing in the first S window f does not pass' if x <= T2 <= y else 'landing elsewhere (FAIL)'] += 1
        c['kind: opening of that window' if T2 == x else ('kind: exit of f inside it' if (8 * g * T2 - 1) % 8 == 0 else 'kind: other (FAIL)')] += 1
        c[('failed window is', 'window 1' if j == 0 else ('the one before W' if j == n - 1 else 'another'))] += 1
for k, v in sorted(c.items(), key=str): print(v, k)
