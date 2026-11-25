"""Outcomes in the wall-window split, test v2 (2026-11-25): v1's W test held S fixed in size.
outcome_split_v1's W populations draw all six readings in (1, H], so S (readings <= 7) shrinks as H grows and the
outcome sets shrink with it.  Here every arrangement has d = 1, three further S readings on the 1/12 grid in (1, 7],
and three F readings on the 1/12 grid in (7, H]; 20,000 per H, seed fixed per H.  Outcome as v1 (S-named only).
Recorded per H: distinct outcomes, outcomes not seen at any smaller H, the largest F-setter lap k, the largest R*.
"""
import random
from fractions import Fraction as Fr
from math import floor
from collections import Counter
exec(open('wall_window_index_v5.py').read().split('def f_run')[0])
def outcome(rs):
    rs = sorted(rs); d = rs[0]; t0 = E / d; S = [r for r in rs if r <= 7 * d]
    T, setters = cascade(rs, t0)
    ws = windows(S, t0, T + 1); i = next(k for k, (a, b, o) in enumerate(ws) if a <= T <= b)
    a, b, o = ws[i]; op = (1, 0) if i == 0 else (S.index(o[0]) + 1, o[1])
    kind = 't0' if T == t0 else ('open' if T == a else 'Fexit')
    k = floor(setters[-1] * T) if kind == 'Fexit' else 0
    return (len(S), i + 1, kind, op), k, 8 * d * T
seen = set()
for H in (16, 40, 80, 160, 320, 640, 1280):
    rng = random.Random(1000 + H); O = Counter(); mk = 0; mR = Fr(0); n = 0
    while n < 20000:
        S = set(Fr(rng.randint(13, 84), 12) for _ in range(3)); F = set(Fr(rng.randint(85, 12 * H), 12) for _ in range(3))
        if len(S) < 3 or len(F) < 3: continue
        n += 1; o, k, R = outcome([Fr(1)] + sorted(S) + sorted(F)); O[o] += 1; mk = max(mk, k); mR = max(mR, R)
    new = [o for o in O if o not in seen]
    print('H', H, '| outcomes', len(O), '| not seen at a smaller H', len(new), new[:6], '| max F lap', mk,
          '| max R*', mR, '=', round(float(mR), 4), '(float steers only)', flush=True)
    seen |= set(O)
print('outcomes over all H:', len(seen))
