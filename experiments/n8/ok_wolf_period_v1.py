#!/usr/bin/env python3
"""THE SECOND RESONANCE: S_x is PERIODIC in x.  Exact Fraction, no float.

alpha_x = 1/4 + S_x/(x |G|),  S_x = sum_i [psi({x v_i}) - psi({x u_i})] over the components
of G(H).  Every endpoint is (8k+-1)/(8e), denominator dividing 8L, L = lcm(H).  So {x u_i}
depends only on x mod 8L:

    >>> S_x is PERIODIC in x, with period dividing 8*lcm(H). <<<

This is a resonance between the speed and the grid's ENDPOINT LATTICE -- multiplicative,
and entirely distinct from the additive relations p.e = 0 that height and relation count
measure.  Consequences:
  * the whole alpha-landscape is finite data (one period of S) under a 1/x envelope;
  * |S_x| <= 3N/16, so alpha_x = 0 forces x <= 3N/(4|G|) -- only FINITELY many free speeds,
    with an explicit bound.
"""
from fractions import Fraction as F
from math import gcd, lcm
from functools import reduce
import sys

def ivs(E):
    out = []
    for e in E:
        for k in range(0, e + 1):
            lo, hi = max(F(8*k-1, 8*e), F(0)), min(F(8*k+1, 8*e), F(1))
            if lo < hi: out.append((lo, hi))
    return out
def merge(iv):
    iv = sorted(iv); m = []
    for lo, hi in iv:
        if m and lo <= m[-1][1]: m[-1][1] = max(m[-1][1], hi)
        else: m.append([lo, hi])
    return m
def complement(m):
    g, cur = [], F(0)
    for lo, hi in m:
        if cur < lo: g.append((cur, lo))
        cur = max(cur, hi)
    if cur < 1: g.append((cur, F(1)))
    return g
def psi(t):
    t = t - int(t)
    if t < 0: t += 1
    if t <= F(1, 8): return 3 * t / 4
    if t <= F(7, 8): return F(1, 8) - t / 4
    return 3 * (t - 1) / 4

def study(H, label):
    G = complement(merge(ivs(H))); MG = sum(v - u for u, v in G); N = len(G)
    L = reduce(lcm, H)
    print(f"\n{label}  H = {H}")
    print(f"  |G| = {MG}   N = {N}   L = lcm(H) = {L}   8L = {8*L}")
    S = lambda x: sum(psi(F(x) * v) - psi(F(x) * u) for u, v in G)
    # true period: smallest p with S_x = S_{x+p} for a long stretch
    ref = [S(x) for x in range(1, 400)]
    per = None
    for p in range(1, 8 * L + 1):
        if (8 * L) % p: continue
        if all(S(x) == S(x + p) for x in range(1, 200)):
            per = p; break
    print(f"  S_x periodic with period {per}"
          f"   (divides 8L: {'yes' if per and (8*L) % per == 0 else 'NO'})"
          f"   8L/period = {8*L//per if per else '-'}")
    bound = F(3 * N, 4) / MG
    free = [x for x in range(1, int(bound) + 40) if S(x) == -F(x) * MG / 4]
    print(f"  alpha_x = 0  forces  x <= 3N/(4|G|) = {bound} = {float(bound):.2f}")
    print(f"  free speeds actually found (alpha_x = 0): {free}"
          f"   max {max(free) if free else '-'}   bound respected: "
          f"{all(x <= bound for x in free)}")
    mx = max(range(1, 4 * (per or 100)), key=lambda x: abs(S(x)))
    print(f"  max |S_x| = {abs(S(mx))} at x={mx}   vs 3N/16 = {F(3*N,16)}")
    return per

for H, lab in (([2, 6, 8, 10, 14], "the E* grid"),
               ([1, 3, 4, 5, 7],   "its base    "),
               ([1, 2, 3, 4, 5],   "an AP prefix")):
    study(H, lab)
