"""Checks of the two directions of the outcome-finiteness reduction (2026-11-25), exact Fractions.
For each case, with R* = 8 d T and the outcome of outcome_split_v1:
  (A) the opener (r, m) of the window holding T satisfies 8m + 1 <= R* r/d <= 7 R*;
  (B) if R* > 7 then the window index is at least 2 and 8m + 1 >= R* - 6;
  (C) T lies in a clear arc of d: R* in [8j+1, 8j+7] for j = floor(R*/8).
Populations: Z16, Q, E340 members.
"""
import itertools, random, pickle
from fractions import Fraction as Fr
from math import floor
exec(open('wall_window_index_v5.py').read().split('def f_run')[0])
def readings(v, k): return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]
from collections import Counter
c = Counter()
def case(pop, rs):
    rs = sorted(rs); d = rs[0]; t0 = E / d; S = [r for r in rs if r <= 7 * d]
    T, _ = cascade(rs, t0); R = 8 * d * T
    ws = windows(S, t0, T + 1); i = next(k for k, (a, b, o) in enumerate(ws) if a <= T <= b)
    r, m = (d, 0) if i == 0 else ws[i][2]
    c[(pop, '(A)', 8 * m + 1 <= R * r / d <= 7 * R)] += 1
    if R > 7: c[(pop, '(B)', i >= 1 and 8 * m + 1 >= R - 6)] += 1
    j = floor(R / 8); c[(pop, '(C)', 8 * j + 1 <= R <= 8 * j + 7)] += 1
for v in itertools.combinations(range(1, 17), 8):
    for k in range(8): case('Z16', [Fr(x) for x in readings(v, k)])
rng = random.Random(1)
for _ in range(3000):
    gaps = [Fr(rng.randint(6, 24), 12) for _ in range(7)]
    v = [Fr(1)]
    for g in gaps: v.append(v[-1] + g)
    for k in range(8): case('Q', readings(v, k))
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
for x in rec: case('E340', [Fr(y) for y in x[1]])
for k, v in sorted(c.items(), key=str): print(v, k)
