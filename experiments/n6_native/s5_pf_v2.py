#!/usr/bin/env python3
"""§5, k >= 2, not uniform at j0. Exact 1D form of the simple pair fold (derived):
  at lap j, u = j + 1/6, runner 1 reads p = alpha u (alpha = v1/v2), runner 4 reads 1/6 + j + lam p (lam = (v4 - v2)/v1),
  window length ell = (2/3 - p/k)/v3, runner 1 sweep r1 = (v1/v3)(2/3 - p/k), runner 4 sweep w = q (2/3 - p/k), q = v4/v3,
  mu = v4/(3 v5).
  fold5 at p:  1/6 <= p - n1 and p - n1 + r1 <= 5/6 for an integer n1 (runner 1 on lap n1), and
               lam p in [m - w + mu, m + 2/3 - mu] for an integer m, and w >= mu.
Check (1) the formula agrees with s5_pf_v1.simple_fold's fold5 on every set; (2) G = {p in [alpha/6, p_max]: fold5 at p}
contains an interval of length >= alpha (then some progression point lies in it); report by alpha and lam."""
import math, sys, random
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("s5_pf_v1.py").read().split("\ndef run(sets")[0])
def fold5_at(S, p):
    v1, v2, v3, v4, v5 = S; D = v3 - v2; k = v1 // D
    lam = F(v4 - v2, v1); q = F(v4, v3); mu = F(v4, 3 * v5)
    h = F(2, 3) - p / k
    if h < 0: return False
    r1 = F(v1, v3) * h; w = q * h
    n1 = math.floor(p - F(1, 6))
    if not (p - n1 + r1 <= F(5, 6)): return False
    if w < mu: return False
    z = lam * p
    m = math.ceil(z - F(2, 3) + mu)
    return m - w + mu <= z
def check(S):
    v1, v2, v3, v4, v5 = S; D = v3 - v2
    al = F(v1, v2)
    agree = True; js = []
    for j, s0, s1 in pair(S):
        p = al * (j + F(1, 6))
        a = fold5_at(S, p)
        x = v4 * s0; w = v4 * (s1 - s0); p1 = frac(v1 * s0); sw1 = v1 * (s1 - s0)
        b = (F(1, 6) <= p1 and p1 + sw1 <= F(5, 6)) and stretch(x, w) >= F(v4, 3 * v5)
        if a != b: agree = False
        if a: js.append(j)
    # G on a fine grid
    pmax = F(2 * (v1 // D), 3); N = 4000
    grid = [pmax * i / N for i in range(N + 1)]
    best = cur = F(0); prev = None
    for p in grid:
        if fold5_at(S, p):
            cur = cur + (pmax / N if prev is not None and prev else 0); prev = True
        else: cur = F(0); prev = False
        best = max(best, cur)
    return agree, js, best >= al, float(al), float(F(v4 - v2, v1))
c = Counter(); fails = []
H = int(sys.argv[1]) if len(sys.argv) > 1 else 40
sets = [S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and s5(S) and S[0] // (S[2] - S[1]) >= 2 and not uni_j0(S)]
for S in sets:
    ag, js, longint, al, lam = check(S)
    c["formula agrees" if ag else "DISAGREES"] += 1
    c[("closes" if js else "no j") + (", G has interval >= alpha" if longint else ", no long interval")] += 1
    if js and not longint and len(fails) < 10: fails.append((S, round(al, 3), round(lam, 3)))
print(f"primitive §5 k>=2 <= {H}, not uniform at j0: {len(sets)}: {dict(c)}")
print("closes but no long interval (examples: S, alpha, lam):", fails)
