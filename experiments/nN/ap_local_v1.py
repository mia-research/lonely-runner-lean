"""Local analysis at the AP's tight end runner, with the instant allowed to move (scale invariant).

Disparities (1..7) deformed to d_k = k*(1 + r_k), exact rationals.  Claim: for small deformations
  class 1: d7 <= 7 d1  ->  t = 1/(8 d1) is lonely  (R1);
  class 7: d7 >= 7 d1  ->  t = (6 + 1/8)/d7 is lonely (opening j = 6 of the largest flank);
so the end runner's isolation never vanishes near the AP; it moves from class 1 to class 7 as d7/d1
crosses 7.  Checked exactly (circDist >= 1/8 as fractions) on random deformations with |r_k| <= rho,
for decreasing rho, to find how far out the two-class rule holds.  Compared with session 2's sign
rule (ap_sign_rule_v1), which fixes the instant at a/8: class 1 iff e1 >= 0 >= e7.
"""
from fractions import Fraction as F
import random
def nd(x): x = x % 1; return min(x, 1 - x)
def lonely(D, t): return all(nd(d * t) >= F(1, 8) for d in D)
rnd = random.Random(38)
for rho in (F(1, 4), F(1, 10), F(1, 20), F(1, 40), F(1, 60), F(1, 100)):
    n = 4000; ok = 0; bad = None; sign_fixed = 0
    for _ in range(n):
        r = [F(rnd.randrange(-10**6, 10**6 + 1), 10**6) * rho for _ in range(7)]
        D = [(k + 1) * (1 + r[k]) for k in range(7)]
        if len(set(D)) < 7 or min(D) <= 0: continue
        d1, d7 = D[0], D[6]
        t = F(1, 8) / d1 if d7 <= 7 * d1 else (6 + F(1, 8)) / d7
        if lonely(D, t): ok += 1
        elif bad is None: bad = [float(x) for x in r]
        e1, e7 = D[0] - 1, D[6] - 7        # absolute deviations, as the sign rule states them
        if (e1 >= 0 >= e7 and lonely(D, F(1, 8))) or (e7 >= 0 >= e1 and lonely(D, F(7, 8))): sign_fixed += 1
    print(f"|r_k| <= {rho}: two-class rule lonely {ok}/{n};  fixed-instant sign rule certifies {sign_fixed}/{n};  first failure r = {bad}")
