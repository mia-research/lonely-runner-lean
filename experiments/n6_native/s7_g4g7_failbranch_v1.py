#!/usr/bin/env python3
"""E54: the 4,000 G4/G7 sets to 120 where the named meeting-time window is short (W < L(rho)/v4). Which native step
closes them: (A) the spread instant 1/(6 v1) (all five read in [1/6, 5/6]; holds iff v5 <= 5 v1); (B) otherwise,
where the lonely instant of the first J123 window lies (runner whose edge bounds it), and the region (v4/v3, v5/v4).
Also over the full exceptional list: how many have v5 <= 5 v1 at all."""
import math
from fractions import Fraction as F
from collections import Counter
s6, s56 = F(1, 6), F(5, 6)
def frac(z): return z - (z.numerator // z.denominator)
def Lform(rho):
    m = max(-(-(rho + 1) // 3) - 1, 0)
    return max(F(1, 3) + 1 / (3 * rho), (m + F(1, 3)) / rho)
def clear_ivs(d, a, b):
    out = []; k = math.floor(a * d - s56)
    while (6*k+1) / (6*d) <= b:
        lo, hi = max(a, (6*k+1)/(6*d)), min(b, (6*k+5)/(6*d))
        if lo <= hi: out.append((lo, hi))
        k += 1
    return out
br = Counter(); reg = Counter(); edge = Counter(); allspread = Counter(); exB = []
for line in open("s7_exceptional_v2_120.out"):
    if not line.startswith("EXC"): continue
    v1, v2, v3, v4, v5, nn, rel = map(int, line.split()[1:8])
    allspread[("v5 <= 5 v1" if v5 <= 5 * v1 else "v5 > 5 v1", "relaxed works" if rel else "short window")] += 1
    if rel: continue
    grp = "G4" if nn == 4 else "G7"
    if v5 <= 5 * v1: br[(grp, "A: spread instant 1/(6 v1)")] += 1; continue
    br[(grp, "B: v5 > 5 v1")] += 1
    S = [F(x) for x in (v1, v2, v3, v4, v5)]
    W = [(F(0), F(4) / S[0])]
    for d in S[:3]: W = [iv for a, b in W for iv in clear_ivs(d, a, b)]
    a, b = next(w for w in W if w[1] > w[0])
    p = [iv for iv in clear_ivs(S[3], a, b) for iv in clear_ivs(S[4], *iv)]
    t = p[0][0]
    who = [i + 1 for i, d in enumerate(S) if frac(d * t) == s6]
    edge[(grp, tuple(who))] += 1
    reg[(grp, round(v4 / v3, 2), round(v5 / v4, 1))] += 1
    if len(exB) < 6: exB.append((v1, v2, v3, v4, v5, str(t * S[2])))
print("all exceptional sets to 120:", dict(allspread))
print("short-window sets by branch:", dict(br))
print("branch B: runner(s) entering at the first lonely instant of the first window:", dict(edge))
print("branch B regions (v4/v3, v5/v4), top:", reg.most_common(10))
print("branch B examples (speeds, instant in units of 1/v3):", exB)
