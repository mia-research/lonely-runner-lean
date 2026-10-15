#!/usr/bin/env python3
"""E38: test the closed form L(rho) = max(1/3 + 1/(3 rho), (m + 1/3)/rho), m = largest integer < (rho+1)/3
(m >= 0), as the supremum over starting readings of the first common clear time of runners 4, 5 (closed bands),
in runner-4 laps, rho = d5/d4 >= 1. Exact sup: f is piecewise linear in (a4, a5); its sup is approached as a start
tends to a critical point (a runner just past its exit). We evaluate f exactly at starts a = 5/6 + eps for both,
for one, and on a dense rational grid, with eps -> 0 (1e-9), over many rho; report max |sup - L| and any start
with f > L (which would refute the formula). Then: E36's failing windows all have l4 < L(d5/d4)."""
import random, ast
from fractions import Fraction as F
from math import floor
s6, s56 = F(1, 6), F(5, 6)
def pieces(a, rate, upto):
    a = a % 1; out = []
    if s6 <= a <= s56: e, x = F(0), (s56 - a) / rate
    else: e = ((s6 - a) % 1) / rate; x = e + F(2, 3) / rate
    while e <= upto:
        out.append((e, x)); e, x = x + F(1, 3) / rate, x + F(1, 3) / rate + F(2, 3) / rate
    return out
def first(a4, a5, rho):
    return min(max(a, c) for a, b in pieces(a4, F(1), F(3)) for c, d in pieces(a5, rho, F(3)) if max(a, c) <= min(b, d))
def Lform(rho):
    m = -(-(rho + 1) // 3) - 1          # largest integer < (rho+1)/3
    m = max(m, 0)
    return max(F(1, 3) + 1 / (3 * rho), (m + F(1, 3)) / rho)
rng = random.Random(9); eps = F(1, 10**9)
worst_gap = F(0); over = []
rhos = [F(p, q) for q in range(1, 9) for p in range(q, 9 * q + 1)] + [F(rng.randint(1000, 9000), 1000) for _ in range(60)]
for rho in sorted(set(rhos)):
    L = Lform(rho); sup = F(0)
    grid = [F(i, 48) for i in range(48)]
    starts = [(s56 + eps, a) for a in grid] + [(a, s56 + eps) for a in grid] + [(s56 + eps, s56 + eps)]
    # critical second-runner phases: aligned so that its blocked window starts at runner 4's re-entry etc.
    for k in range(0, 4):
        for off in (F(0), F(1, 3)):
            starts.append((s56 + eps, (s56 + eps - rho * (off + F(k, 1) / rho * 0)) % 1))
            starts.append((s56 - (rho * 0) , (s56 + eps - rho * off) % 1))
    for a4 in grid:
        for a5 in grid[::3]: starts.append((a4, a5))
    # the resonant construction: 5 just entered its blocked window at u = 0, 4 clear with c just below 1/(3 rho)
    m = max(-(-(rho + 1) // 3) - 1, 0)
    for frac_c in (F(999, 1000), F(1, 2), F(1, 1000)):
        c = frac_c / (3 * rho)
        starts.append(((s56 - c) % 1, (s56 + eps) % 1))
    for a4, a5 in starts:
        f = first(a4, a5, rho)
        sup = max(sup, f)
        if f > L: over.append((rho, a4, a5, f, L))
    worst_gap = max(worst_gap, L - sup)
print(f"rhos tested {len(set(rhos))}; starts with f > L(rho): {len(over)}", over[:5])
print(f"largest L(rho) - (sup found): {float(worst_gap):.2e}")
print("L at sample rho:", {str(r): str(Lform(F(r))) for r in ["1", "3/2", "2", "5/2", "3", "4", "11/2", "7"]})
print("max over all rho >= 1 of L(rho) equals 2/3 at rho = 1:", max(Lform(r) for r in rhos) == F(2, 3))
rows = [l.rstrip("\n").split("\t") for l in open("six_s5_window45_v1.tsv")][1:]
bad = 0; nf = 0; nsucc_over = 0; nwin_over = 0
for r in rows:
    S = ast.literal_eval(r[0]); l4 = F(r[6]); rho = F(S[4], S[3])
    if r[8] == "False":
        nf += 1; bad += l4 >= Lform(rho)
    if l4 >= Lform(rho): nwin_over += 1; nsucc_over += r[8] == "True"
print(f"E36 failing windows: {nf}; with l4 >= L(rho): {bad}. Windows with l4 >= L(rho): {nwin_over}, all succeed: {nsucc_over == nwin_over}")
