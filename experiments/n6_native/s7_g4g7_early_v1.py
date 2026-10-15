#!/usr/bin/env python3
"""E53: the G4/G7 sets where the named meeting-time window is too short for window_two (W < L(rho)/v4). For each:
the J123 windows in time order from t = 0 (all runners start at 0: no free phase); the first one that contains an
instant with runners 4 and 5 also clear (an exact lonely instant), its index, its start in units of 1/v3, and
whether it is BHK's early window ([2/3, 35/48]/v3 for G4, [2/3, 65/84]/v3 for G7) or contains it. Also: is the first
J123 window that reaches a lonely instant always before the named meeting time."""
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
idx = Counter(); early = Counter(); start = Counter(); n = 0; bad = []
for line in open("s7_exceptional_v2_80.out"):
    if not line.startswith("EXC"): continue
    v1, v2, v3, v4, v5, nn, rel = map(int, line.split()[1:8])
    if rel: continue
    n += 1; S = [F(x) for x in (v1, v2, v3, v4, v5)]
    grp = "G4" if nn == 4 else "G7"
    E = (F(2, 3) / S[2], (F(35, 48) if grp == "G4" else F(65, 84)) / S[2])
    W = [(F(0), F(4, 1) / S[0])]
    for d in S[:3]: W = [iv for a, b in W for iv in clear_ivs(d, a, b)]
    W = [w for w in W if w[1] > w[0]]
    found = None
    for i, (a, b) in enumerate(W):
        p = [iv for iv in clear_ivs(S[3], a, b) for iv in clear_ivs(S[4], *iv)]
        if p: found = (i, a, b); break
    if found is None: bad.append((v1, v2, v3, v4, v5)); continue
    i, a, b = found
    idx[(grp, i)] += 1
    start[(grp, round(float(a * S[2]), 2))] += 1
    early[(grp, "first lonely window contains BHK's early window" if a <= E[0] and E[1] <= b else
           ("overlaps it" if a < E[1] and E[0] < b else "elsewhere"))] += 1
print(f"G4/G7 sets with W < L/v4: {n}; no lonely instant found in windows up to 4/v1: {len(bad)} {bad[:5]}")
print("index of the first J123 window with a lonely instant (0 = first after t = 0):", dict(sorted(idx.items())))
print("its start, in units of 1/v3:", dict(sorted(start.items())[:20]))
print("relation to BHK's early window:", dict(early))
