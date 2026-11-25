"""Why no single fast reading passes (2026-11-25), on E340's 7,644 slow sets.  For each S, at the window W where the
f-set empties (v2), classify: 'alone' if no f in (7, 10^4) passes W at all (allowed(W) empty), else 'intersection'
(each window is passable alone, the passes do not meet).  For 'alone', report the length ratio b/a of W against the
largest pass ratio (8k+1)/(8k-1) available to an f > 7 at W, i.e. k with (8k+1)/(8b) > 7.
"""
import pickle
from fractions import Fraction as Fr
from collections import Counter
exec(open('one_fast_reach_v2.py').read().split('from collections import Counter')[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
seen = set(); c = Counter(); arc = Counter(); worst = None
for r in rec:
    rs = sorted(Fr(x) for x in r[1]); S = [x for x in rs if x <= 7]
    if len(S) != 6 or tuple(S) in seen: continue
    seen.add(tuple(S))
    Bd, n, A, ws = bound(S)
    a, b, o = ws[n]
    alone = not allowed(a, b, Fr(10) ** 4)
    kind = 'alone' if alone else 'intersection'
    c[kind] += 1; arc[(kind, 'arc0' if b <= Fr(7, 8) else 'arc1')] += 1
    if not alone and (worst is None or Bd > worst[0]): worst = (Bd, S, n)
print('blocking window kinds:', dict(c)); print('by arc:', dict(arc))
if worst: print('largest bound among intersection kind:', worst[0], '~', round(float(worst[0]), 6), '(float steers only), window index', worst[2] + 1)
