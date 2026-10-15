#!/usr/bin/env python3
"""E39: the two-window statement in cut-stretch terms, checked on the §5 sets that have no single long-enough J123
window (E38: 582 sets).
First common clear time f(a4, a5) of runners 4, 5 from start readings (a4, a5), in runner-4 laps, rho = d5/d4:
the four-candidate construction of `window_two` (exact as a formula; evaluated in floating point here).
A geometry (alpha, beta, gamma, rho): windows W1 = [0, alpha], W3 = [alpha+beta, alpha+beta+gamma] (runner-4 laps).
It is SAFE (phase-free) if for every start (a4, a5) at least one window contains a common clear point:
f(a4, a5) <= alpha or f(a4 + alpha + beta, a5 + rho (alpha + beta)) <= gamma. Checked on an N x N phase grid
(numeric: a failing region thinner than 1/N can be missed; margins are reported).
For each of the 582 sets: all pairs of J123 windows within one period (each pair = a geometry with the set's rho);
the set is covered if some pair is SAFE. Also checked: the set's own phases (the actual readings) as a control
that the per-window test agrees with exact band intersection.
Usage: six_two_window_v1.py N"""
import sys, math
import numpy as np
from fractions import Fraction as F
from collections import Counter
N = int(sys.argv[1])
s6, s56 = F(1, 6), F(5, 6)
def first_common(a4, a5, rho):
    a4 = np.mod(a4, 1.0); a5 = np.mod(a5, 1.0)
    p = np.ceil(a4 - 5/6 - 1e-12)
    s = np.maximum(a4, p + 1/6); t1 = s - a4; e = p + 5/6 - a4
    y1 = a5 + rho * t1; fy1 = np.mod(y1, 1.0)
    c1 = (fy1 >= 1/6 - 1e-12) & (fy1 <= 5/6 + 1e-12)
    q = np.round(y1); t2 = (q + 1/6 - a5) / rho
    c2 = (~c1) & (t2 <= e + 1e-12)
    t3 = p + 7/6 - a4; y3 = a5 + rho * t3; fy3 = np.mod(y3, 1.0)
    c3 = (fy3 >= 1/6 - 1e-12) & (fy3 <= 5/6 + 1e-12)
    q3 = np.round(y3); t4 = (q3 + 1/6 - a5) / rho
    return np.where(c1, t1, np.where(c2, t2, np.where(c3, t3, t4)))
g = (np.arange(N) + 0.5) / N
A4, A5 = np.meshgrid(g, g, indexing="ij")
def safe(alpha, beta, gamma, rho):
    f1 = first_common(A4, A5, rho)
    f3 = first_common(A4 + alpha + beta, A5 + rho * (alpha + beta), rho)
    bad = (f1 > alpha + 1e-12) & (f3 > gamma + 1e-12)
    return not bad.any(), float(np.min(np.maximum(f1 - alpha, f3 - gamma)))
def clear_ivs(d, a, b):
    out = []; k = math.floor(a * d - s56)
    while (6*k+1) / (6*d) <= b:
        lo, hi = max(a, (6*k+1)/(6*d)), min(b, (6*k+5)/(6*d))
        if lo < hi: out.append((lo, hi))
        k += 1
    return out
def pieces(a, rate, upto):
    a = a % 1; out = []
    if s6 <= a <= s56: e, x = F(0), (s56 - a) / rate
    else: e = ((s6 - a) % 1) / rate; x = e + F(2, 3) / rate
    while e <= upto: out.append((e, x)); e, x = x + F(1, 3) / rate, x + F(1, 3) / rate + F(2, 3) / rate
    return out
def f_exact(a4, a5, rho):
    return min(max(a, c) for a, b in pieces(a4, F(1), F(3)) for c, d in pieces(a5, rho, F(3)) if max(a, c) <= min(b, d))
def Lform(rho):
    m = max(-(-(rho + 1) // 3) - 1, 0)
    return max(F(1, 3) + 1 / (3 * rho), (m + F(1, 3)) / rho)
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
cov = Counter(); ctrl = Counter(); gaps_pat = Counter(); unc = []; geo = Counter()
for r in rows:
    if r[1] != "S5": continue
    S = [F(x) for x in eval(r[0])]; gcd = math.gcd(*[int(x) for x in S]); P = F(1, gcd)
    ivs = [(F(0), 2 * P)]
    for d in S[:3]: ivs = [iv for a, b in ivs for iv in clear_ivs(d, a, b)]
    rho = S[4] / S[3]
    if max((S[3] * (b - a) for a, b in ivs), default=0) >= Lform(rho): continue   # covered by one window (E38)
    W = [w for w in ivs if w[0] < P]
    # control: the per-window test at the set's own phases matches exact band intersection
    for a, b in W[:6]:
        fe = f_exact(S[3]*a % 1, S[4]*a % 1, rho)
        fn = first_common(np.array([float(S[3]*a % 1)]), np.array([float(S[4]*a % 1)]), float(rho))[0]
        ctrl["float f = exact f" if abs(fn - float(fe)) < 1e-9 else "DIFFER"] += 1
    found = False; best = None
    for i in range(len(W)):
        for j in range(i + 1, min(i + 4, len(W) + 2)):
            a1, b1 = W[i]; a3, b3 = W[j % len(W)]
            if j >= len(W): a3, b3 = a3 + P, b3 + P
            al, be, ga = float(S[3]*(b1 - a1)), float(S[3]*(a3 - b1)), float(S[3]*(b3 - a3))
            ok, marg = safe(al, be, ga, float(rho))
            if ok:
                found = True; geo[(j - i)] += 1; break
        if found: break
    kk = S[0] / (S[2] - S[1])
    cov[("covered by a SAFE pair" if found else "no SAFE pair", "BHK k = %s" % (kk if kk.denominator == 1 and kk >= 3 else ("1 or 2 (Prop 11)" if kk in (1, 2) else kk)))] += 1
    if not found and len(unc) < 10: unc.append(tuple(int(x) for x in S))
print(f"grid N = {N}")
print("control, first common time at the sets own phases:", dict(ctrl))
print("the 582 sets:", dict(cov))
print("SAFE pair found at window distance (j - i):", dict(geo))
print("uncovered examples:", unc)
