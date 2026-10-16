#!/usr/bin/env python3
"""Continuous failures of the pair-window fold at k = 2 with alpha/alpha_max <= 0.6 (s5_pf_v3 grid): list them with
beta, lam = beta/alpha, mu, and the usable laps j (runner 1 clear across P_j) with the offset z = beta u (mod 1) and arc
[mu - w, 2/3 - mu]; then whether integer sets exist there: the near-runner bound and the integrality (v1 = kD, v2 = kD/alpha,
v4 - v2 = beta v2 >= D + 1 ... reported as the smallest D with v2 = kD/alpha an integer within 1%)."""
import math
exec(open("s5_pf_v3.py").read().split("for k in (2,")[0])
k = 2; amax = k / (3 * k - 1); rows = []
for ai in range(1, 37):
    al = amax * ai / 60
    for bi in range(1, 80):
        be = al / k + 1.2 * bi / 80
        if not nonuniform(k, al, be): continue
        for mi in range(1, 21):
            mu = mi / 60
            if not closes(k, al, be, mu): rows.append((round(al / amax, 3), round(al, 4), round(be, 4), round(be / al, 3), round(mu, 3)))
print(len(rows), "failures with alpha/amax <= 0.6")
for r in rows: print("  alpha/amax, alpha, beta, lam, mu =", r)
def usable(k, al, be, mu):
    rho = al / (1 + al / k); q = (1 + be) / (1 + al / k); out = []; j = 0
    while True:
        u = j + 1 / 6; p = al * u; h = 2 / 3 - p / k
        if h < 0: return out
        n1 = math.floor(p - 1 / 6)
        if p - n1 + rho * h <= 5 / 6:
            out.append((j, n1, round((be * u) % 1, 3), round(mu - q * h, 3), round(2 / 3 - mu, 3), round(q * h, 3)))
        j += 1
for r in rows[:6]:
    _, al, be, lam, mu = r
    print("  ", r, "usable (j, n1, z, arc lo, arc hi, w):", usable(k, al, be, mu)[:12])
