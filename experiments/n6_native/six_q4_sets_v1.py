#!/usr/bin/env python3
"""E40: the six §5 sets not covered by one or two windows (E39), all with v1/v3 = 1/4 (BHK's q = 4, Lemma 13).
Times in BHK's units (v3 = 1: tau = v3 * t). For each set, over one period: every J123 window (runners 1-3 clear),
its length in runner-4 laps against L(rho), and the lonely intervals inside it (runners 4, 5 also clear), with the
runners that bound each lonely interval (entering at its start, leaving at its end). BHK's Lemma 13 windows
I1 = [2/3, 5/6] and I2 = [13/6, 44/18] are marked. Also r = 4 v4/v3 and s = 4 v5/v3 (BHK's v4 = r/4, v5 = s/4)."""
import math
from fractions import Fraction as F
s6, s56 = F(1, 6), F(5, 6)
def clear_ivs(d, a, b):
    out = []; k = math.floor(a * d - s56)
    while (6*k+1) / (6*d) <= b:
        lo, hi = max(a, (6*k+1)/(6*d)), min(b, (6*k+5)/(6*d))
        if lo <= hi: out.append((lo, hi))
        k += 1
    return out
def Lform(rho):
    m = max(-(-(rho + 1) // 3) - 1, 0)
    return max(F(1, 3) + 1 / (3 * rho), (m + F(1, 3)) / rho)
sets = [(1,3,4,5,6), (2,6,8,10,11), (4,12,16,20,23), (4,12,16,20,25), (5,15,20,24,26), (7,21,28,36,40)]
for S0 in sets:
    v3 = F(S0[2]); V = [F(x) / v3 for x in S0]            # BHK units, v3 = 1
    g = math.gcd(*S0); P = F(S0[2], g)                    # period in BHK time units: v3 * (1/g)
    r, s = 4 * V[3], 4 * V[4]; rho = V[4] / V[3]
    print(f"== {S0}: BHK units v = {[str(x) for x in V]}; v1 = {V[0]}; r = 4 v4 = {r}, s = 4 v5 = {s}; period {P}; L(rho) = {Lform(rho)} ({float(Lform(rho)):.3f})")
    W = [(F(0), P)]
    for d in V[:3]: W = [iv for a, b in W for iv in clear_ivs(d, a, b)]
    for a, b in W:
        if a == b: continue
        lw = V[3] * (b - a)
        lon = [iv for x, y in [(a, b)] for iv in clear_ivs(V[3], x, y)]
        lon = [iv for x, y in lon for iv in clear_ivs(V[4], x, y)]
        mark = " [BHK I1]" if (a <= F(2, 3) <= b) else (" [BHK I2]" if a <= F(13, 6) <= b else "")
        desc = []
        for x, y in lon:
            def who(t, kind):
                out = []
                for i, d in enumerate(V):
                    fr = d * t - math.floor(d * t)
                    if kind == "in" and fr == s6: out.append(i + 1)
                    if kind == "out" and fr == s56: out.append(i + 1)
                return out
            desc.append(f"[{x}, {y}] len {float(y - x):.4f} enter {who(x, 'in')} leave {who(y, 'out')}")
        print(f"   J123 [{a}, {b}] ({float(a):.3f}-{float(b):.3f}) length {float(lw):.3f} runner-4 laps{mark}: lonely {desc if desc else 'none'}")
