#!/usr/bin/env python3
"""The lam = +-1 guarantee over the continuous parameters. Runner 4's arcs depend only on c, q4 = v4/v3 (near-runner:
1 < q4 < 4c/(4c-1)) and mu = v4/(3 v5) in (0, 1/3]: lambda4 = q4 (5/6 - (c+1)/(6c)), v4 s0 = q4 (c+1)/(6c),
v4 s1 = 5 q4 / 6. U = {p in [1/6,5/9]: lam p in A} union {p in [4/9,5/6]: lam p in A'}. Grid search for the smallest
longest-interval of U, for lam = 1 and lam = -1; a value >= 1/15 means every D >= 15 has a grid point j/D in U."""
from fractions import Fraction as F
import math
def frac(x): return x - math.floor(x)
def pre(I, lam, x, L):
    a, b = I; out = []
    if L >= 1: return [I]
    for sh in range(-3, 4):
        lo, hi = x + sh, x + L + sh
        if lam == -1: lo, hi = -hi, -lo
        l2, h2 = max(a, lo), min(b, hi)
        if l2 < h2: out.append((l2, h2))
    return out
def longest(iv):
    iv = sorted(iv); best = 0; cur = None
    for a, b in iv:
        if cur and a <= cur[1] + 1e-15: cur = (cur[0], max(cur[1], b))
        else:
            if cur: best = max(best, cur[1] - cur[0])
            cur = (a, b)
    if cur: best = max(best, cur[1] - cur[0])
    return best
worst = {1: (9, None), -1: (9, None)}
for c in list(range(1, 41)) + [100, 1000, 10**6]:
    qmax = 4 * c / (4 * c - 1)
    for i in range(0, 201):
        q4 = 1 + (qmax - 1) * i / 200
        lam4 = q4 * (5 / 6 - (c + 1) / (6 * c)); vs0 = q4 * (c + 1) / (6 * c); vs1 = 5 * q4 / 6
        for jj in range(1, 101):
            mu = (1 / 3) * jj / 100
            A = (1 / 6 - lam4 + mu - vs0, 5 / 6 - mu - vs0); Ap = (1 / 6 - lam4 + mu + vs1, 5 / 6 - mu + vs1)
            for lam in (1, -1):
                U = pre((1 / 6, 5 / 9), lam, A[0], A[1] - A[0]) + pre((4 / 9, 5 / 6), lam, Ap[0], Ap[1] - Ap[0])
                m = longest(U)
                if m < worst[lam][0]: worst[lam] = (m, (c, round(q4, 4), round(mu, 4)))
for lam in (1, -1): print(f"lam {lam}: smallest longest interval of U = {worst[lam][0]:.4f} (1/15 = {1/15:.4f}) at (c, q4, mu) = {worst[lam][1]}")
