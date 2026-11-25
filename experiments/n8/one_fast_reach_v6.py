"""E939 rule-22 item (2026-11-25): the near-vertex points of v5 where B(S) >= 26433/2209.  Same 200 points (seed 1).
At each such point: f = rho_7 = 2209/297 no longer passes (perturbing S moves the pass intervals), so the f used is
the midpoint of each interval of A just before W.  Reported: the cascade's R* for that f, whether R* <= 26433/2209,
and B - R* (B is the right end 8b of the window W where the landing sits, not the landing).
"""
import random
from fractions import Fraction as Fr
exec(open('one_fast_reach_v5.py').read().split("print('S =',")[0])
random.seed(1)
for _ in range(200):
    T = sorted([Fr(1)] + [x * (1 + Fr(random.randint(-1000, 1000), 10 ** 7)) for x in S[1:]])
    Bd, n, A, ws = bound(T)
    if Bd is None or Bd < Fr(26433, 2209): continue
    for l, h in A:
        f = (l + h) / 2; L, _ = cascade(sorted(T + [f]), E); R = 8 * L; a, b, o = ws[n]
        print('B =', Bd, '| f =', f, '| R* =', R, '| R* <= 26433/2209:', R <= Fr(26433, 2209), '| T in W:', a <= L <= b, '| B - R* =', Bd - R)
