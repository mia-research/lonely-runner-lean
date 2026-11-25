"""Consistency check of v2's per-S bound at E344's extremal vertex (2026-11-25).  Vertex (E344): rho_5 = 47/9,
rho_3 = 47/15, rho_7 = 2209/297, rho_6 = 7 rho_7/9, rho_4 = 47 rho_6/65, rho_2 = 23 rho_4/41; only rho_7 exceeds 7,
so S = {1, rho_2, ..., rho_6} and F = {rho_7}.  The tree supremum 26433/2209 = 89/rho_7 is the closure value of
cells next to this point, so B(S) must be at least it (B is a bound for S + {f} over every f, and B depends on S
continuously only window by window).  Reported: B(S) at the vertex, and at 200 exact points near it.
"""
import random
from fractions import Fraction as Fr
exec(open('one_fast_reach_v2.py').read().split('from collections import Counter')[0])
r5 = Fr(47, 9); r3 = Fr(47, 15); r7 = Fr(2209, 297); r6 = 7 * r7 / 9; r4 = 47 * r6 / 65; r2 = 23 * r4 / 41
S = sorted([Fr(1), r2, r3, r4, r5, r6]); print('S =', [str(x) for x in S], '| f =', r7, '| 89/f =', Fr(89) / r7)
Bd, n, A, ws = bound(S); print('B(S) at the vertex =', Bd, '~', round(float(Bd), 6), '(float steers only), window', n + 1)
random.seed(1); worst = None; ok = 0
for _ in range(200):
    T = sorted([Fr(1)] + [x * (1 + Fr(random.randint(-1000, 1000), 10 ** 7)) for x in S[1:]])
    B2 = bound(T)[0]
    if B2 is not None and B2 >= Fr(26433, 2209): ok += 1
    if worst is None or (B2 is not None and B2 > worst): worst = B2
print('near points with B >= 26433/2209:', ok, 'of 200 | largest B near the vertex:', worst, '~', round(float(worst), 6))
print('--- why B = 225/47 at the vertex: f = rho_7 against each window up to the blocking one')
for i, (a, b, o) in enumerate(ws[:n + 1]):
    iv = allowed(a, b, Fr(10) ** 4); inside = [(l, h) for l, h in iv if l < r7 < h]; edge = [(l, h) for l, h in iv if r7 in (l, h)]
    print('window', i + 1, (str(a), str(b)), '| f strictly inside a pass interval:', bool(inside), '| f on an endpoint:', [(str(l), str(h)) for l, h in edge])
