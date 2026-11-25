"""Wall-window law, test v4c (2026-11-25): v4b with the Q arrangements started at speed 1, not 0 (rule 5). Readings are differences, so counts must match v4b."""
import sys
src = open('wall_window_law_v4.py').read()
src = src.split("tab = Counter(); ex = {}")[0]
exec(src)
from collections import Counter
c = Counter()
def case(pop, rs, label):
    rs = sorted(rs); d = rs[0]; t0 = E / d
    S = [r for r in rs if r <= 7 * d]; Fs = [r for r in rs if r > 7 * d]
    T, st = cascade(rs, t0)
    c[(pop, 'T <= 7/(8d)' if T <= Fr(7, 8) / d else 'T > 7/(8d)')] += 1
    if not Fs: return
    ws = windows(S, t0, T + 1)
    i = next(k for k, (a, b, o) in enumerate(ws) if a <= T <= b)
    c[(pop, 'window %d' % min(i + 1, 3), 'T = opening' if T == ws[i][0] else 'T = F exit')] += 1
def readings(v, k): return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]
import itertools, random
for v in itertools.combinations(range(1, 17), 8):
    for k in range(8): case('Z16', [Fr(x) for x in readings(v, k)], (v, k))
rng = random.Random(1)
for _ in range(3000):
    gaps = [Fr(rng.randint(6, 24), 12) for _ in range(7)]
    v = [Fr(1)]   # first runner at speed 1 (rule 5); readings unchanged
    for g in gaps: v.append(v[-1] + g)
    for k in range(8): case('Q', readings(v, k), 0)
rng = random.Random(6); seen = 0
while seen < 2900:
    others = sorted(set(Fr(rng.randint(13, 480), 12) for _ in range(6)))
    if len(others) < 6: continue
    seen += 1; case('W40', [Fr(1)] + others, seen)
for k, v in sorted(c.items()): print(v, k)
