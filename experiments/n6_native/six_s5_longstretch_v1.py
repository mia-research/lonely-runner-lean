#!/usr/bin/env python3
"""E38 step 2 check: in every §5 set (integer speeds, period 1/g), is there a J123 window (runners 1-3 all clear) of
length at least L(rho)/d4, rho = d5/d4, so that `window_two` applies directly? For each set: the longest J123 window
in one period, in runner-4 laps, against L(rho); also against BHK's uniform 2/3. Sets without such a window are
listed: they are where §5 needs more than the window lemma (races, triple configurations)."""
import math
from fractions import Fraction as F
from collections import Counter
s6, s56 = F(1, 6), F(5, 6)
def Lform(rho):
    m = max(-(-(rho + 1) // 3) - 1, 0)
    return max(F(1, 3) + 1 / (3 * rho), (m + F(1, 3)) / rho)
def clear_ivs(d, a, b):
    out = []; k = math.floor(a * d - s56)
    while (6*k+1) / (6*d) <= b:
        lo, hi = max(a, (6*k+1)/(6*d)), min(b, (6*k+5)/(6*d))
        if lo < hi: out.append((lo, hi))
        k += 1
    return out
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
c = Counter(); ex = []; ratio_short = Counter()
for r in rows:
    if r[1] != "S5": continue
    S = [F(x) for x in eval(r[0])]; g = math.gcd(*[int(x) for x in S]); P = F(1, g)
    ivs = [(F(0), 2 * P)]
    for d in S[:3]:
        ivs = [iv for a, b in ivs for iv in clear_ivs(d, a, b)]
    best = max((S[3] * (b - a) for a, b in ivs), default=F(0))
    rho = S[4] / S[3]; L = Lform(rho)
    c[("some J123 window >= L(rho)" if best >= L else "none >= L(rho)", "and >= 2/3" if best >= F(2, 3) else "but < 2/3")] += 1
    if best < L:
        ratio_short[round(float(best / L), 1)] += 1
        if len(ex) < 8: ex.append((tuple(int(x) for x in S), float(best), float(L)))
print("§5 sets:", sum(c.values()))
print(dict(c))
print("sets with no long-enough window: longest / L(rho) ->", dict(sorted(ratio_short.items())))
for e in ex: print("  e.g.", e)
