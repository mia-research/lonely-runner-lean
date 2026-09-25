"""The block-split rule on the constructed residual members (residual_members_v1).

Split S = C (core, c runners) + F (block, f runners), g = gcd(F).  Order c+1 gives an instant tau
with every core reading >= 1/(c+1); each core runner then stays >= 1/8 on
[tau - delta, tau + delta], delta = (1/(c+1) - 1/8)/max(C).  The block repeats with period 1/g, and
order f+1 gives sigma in [0,1) with every F/g reading >= 1/(f+1) >= 1/8.  If 2*delta >= 1/g, some
t = (sigma + m)/g lies in the window, and t is lonely.  Condition: g >= 4(c+1) max(C)/(7-c)
(c = 5: g >= 12 max C).  Here every step is exact: tau and sigma are found as openings (Theorem 9)
by exact Fraction search, t is built, and all seven readings are checked by the integer band test.
"""
from fractions import Fraction as Fr
from math import gcd, floor, ceil
from functools import reduce
exec(open('residual_members_v1.py').read().split("L = 8 * lcm")[0])
from math import lcm
def nd(x): x = x % 1; return min(x, 1 - x)
def lonely_opening(D, thr):
    """least opening (j + thr)/e, e in D, at which every d in D reads >= thr (Theorem 9 form)."""
    best = None
    for e in D:
        for j in range(e):
            t = (j + thr) / e
            if all(nd(d * t) >= thr for d in D) and (best is None or t < best): best = t; break
    return best
def split_instant(S, F):
    C = [d for d in S if d not in F]; c = len(C); g = reduce(gcd, F)
    tau = lonely_opening(C, Fr(1, c + 1)); delta = (Fr(1, c + 1) - Fr(1, 8)) / max(C)
    sigma = lonely_opening([f // g for f in F], Fr(1, len(F) + 1))
    m = ceil((tau - delta) * g - sigma)
    t = (sigma + m) / g
    if not (tau - delta <= t <= tau + delta): return None
    return t
L = 8 * lcm(*range(1, 65)); rnd = random.Random(30)
members = []; tried = 0
while tried < 3000:
    C0 = rnd.sample(range(1, 101), 5); u = rnd.randrange(1, 50); u2 = rnd.randrange(u + 1, 7 * u + 1)
    S = tuple(sorted(C0 + [L * u, L * u2])); tried += 1
    if residual(S): members.append(S)
ok = 0; bad = []
for S in members:
    F = [d for d in S if d >= L]
    t = split_instant(S, F)
    if t is not None and t > 0 and all(8 * nd(d * t) >= 1 for d in S): ok += 1
    else: bad.append(S)
print(f"residual members (same construction and seed as residual_members_v1): {len(members)}")
print(f"block split (core of 5 at 1/6, pair at 1/3, g >= 12 max C) gives an exactly verified lonely instant: {ok}/{len(members)}")
print(f"failures: {bad[:3]}")
S = members[0]; F = [d for d in S if d >= L]; t = split_instant(S, F)
print(f"example: core {[d for d in S if d < L]}, pair L*{[d // L for d in F]}: t has denominator of {len(str(t.denominator))} digits; min reading {min(nd(d * t) for d in S)}")
