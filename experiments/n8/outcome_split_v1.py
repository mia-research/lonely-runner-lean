"""Outcomes in the wall-window split, test v1 (2026-11-25).  Exact Fractions; the cascade is the oracle.

Owner (2026-11-25): existence comes from the AP and phi(n); the question is arrangement finiteness (G2).  M089 left
open "whether the A outcomes reduce to finitely many once the d_max lap is quotiented out"; M071 names the d_max side.
E929-E931 [P]: with d = d_min, S = readings <= 7d, F = the rest, the landing T is t0 = 1/(8d), the opening
(8m+1)/(8r) of an S window (r in S), or an F exit inside the S window holding T.
OUTCOME (S-named only; no F lap enters):  (|S|, i, kind, opener) with
   i      = index of the S window holding T (window 1 starts at t0);
   kind   = 't0' (T = t0), 'open' (T = the window's opening, i >= 2), 'Fexit' (T inside the window, an F exit);
   opener = (rank of the opening reading within S, its lap m), or (1, 0) for window 1.
Also recorded, NOT part of the outcome: the lap k of T's setter when it is an F reading (the d_max lap), and R* =
8 d T.  Counted per population: cases, distinct outcomes, outcomes shared with the other populations, max k, max R*.
Populations: Z16, Q (positions from 1, rule 5), W40..W640 (1 and six readings on the 1/12 grid in (1, H]), and E340's
110,081 members (one witness per tree cell, readings r[1], d_min = 1).
"""
import itertools, random, sys, pickle
from fractions import Fraction as Fr
from math import floor
from collections import Counter
exec(open('wall_window_index_v5.py').read().split('def f_run')[0])
def readings(v, k): return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]
st = {}
def case(pop, rs):
    rs = sorted(rs); d = rs[0]; t0 = E / d
    S = [r for r in rs if r <= 7 * d]
    T, setters = cascade(rs, t0)
    ws = windows(S, t0, T + 1)
    i = next(k for k, (a, b, o) in enumerate(ws) if a <= T <= b)
    a, b, o = ws[i]
    if i == 0: opener = (1, 0)
    else: opener = (S.index(o[0]) + 1, o[1])
    kind = 't0' if T == t0 else ('open' if T == a else 'Fexit')
    out = (len(S), i + 1, kind, opener)
    k = None
    if kind == 'Fexit':
        s = setters[-1]; assert s > 7 * d; k = floor(s * T)
    s_ = st.setdefault(pop, dict(n=0, O=Counter(), maxk=0, maxR=Fr(0), kinds=Counter()))
    s_['n'] += 1; s_['O'][out] += 1; s_['kinds'][kind] += 1
    if k is not None: s_['maxk'] = max(s_['maxk'], k)
    s_['maxR'] = max(s_['maxR'], 8 * d * T)
pops = sys.argv[1:] or ['Z16', 'Q', 'W40', 'W80', 'W160', 'W320', 'W640', 'E340']
if 'Z16' in pops:
    for v in itertools.combinations(range(1, 17), 8):
        for k in range(8): case('Z16', [Fr(x) for x in readings(v, k)])
if 'Q' in pops:
    rng = random.Random(1)
    for _ in range(3000):
        gaps = [Fr(rng.randint(6, 24), 12) for _ in range(7)]
        v = [Fr(1)]
        for g in gaps: v.append(v[-1] + g)
        for k in range(8): case('Q', readings(v, k))
for H, seed in ((40, 6), (80, 7), (160, 8), (320, 9), (640, 10)):
    if 'W%d' % H not in pops: continue
    rng = random.Random(seed); seen = 0
    while seen < 2900:
        others = sorted(set(Fr(rng.randint(13, 12 * H), 12) for _ in range(6)))
        if len(others) < 6: continue
        seen += 1; case('W%d' % H, [Fr(1)] + others)
if 'E340' in pops:
    rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
    for r in rec: case('E340', [Fr(x) for x in r[1]])
allO = Counter()
for pop, s in st.items():
    for o in s['O']: allO[o] += 1
for pop, s in st.items():
    only = [o for o in s['O'] if allO[o] == 1]
    print(pop, '| cases', s['n'], '| outcomes', len(s['O']), '| only here', len(only), '| kinds', dict(s['kinds']),
          '| max F-setter lap k', s['maxk'], '| max R*', s['maxR'], '=', float(s['maxR']).__round__(4), '(float steers only)')
names = list(st)
for a, b in itertools.combinations(names, 2):
    A, B = set(st[a]['O']), set(st[b]['O'])
    print('  ', a, b, 'shared', len(A & B), '| only', a, len(A - B), '| only', b, len(B - A))
print('outcomes in total', len(allO))
for pop, s in st.items():
    print(pop, 'outcomes (count, (|S|, window, kind, opener rank/lap)):')
    for o, c in sorted(s['O'].items(), key=lambda x: (-x[1], str(x[0]))): print('   ', c, o)
