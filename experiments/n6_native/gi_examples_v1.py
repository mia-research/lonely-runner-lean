#!/usr/bin/env python3
"""Owner's examples: (1..7, 16) and (1..5, 16, 64, 720). For each, as an arrangement of 8 runners: residues mod 8,
and every instant in one period at which all pairs are at least 1/8 apart (global isolation, n = 8), computed exactly
on the candidate grid of all events (instants where some pair is exactly 1/8 or 7/8 apart are interval ends; test
midpoints and ends). Also, read as 8 disparities from a subject at speed 0 (order 9): lonely at 1/9 and where."""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
def frac(z): return z - (z.numerator // z.denominator)
def cd(z): f = frac(z); return min(f, 1 - f)
def instants(sp, thr, period):
    diffs = sorted({abs(a - b) for a, b in combinations(sp, 2)})
    cand = set()
    for d in diffs:
        for k in range(d * period.numerator // period.denominator + 2):
            for c in (thr, 1 - thr):
                t = (k + c) / F(d)
                if 0 <= t <= period: cand.add(t)
    cand = sorted(cand); pts = set(cand) | {(a + b) / 2 for a, b in zip(cand, cand[1:])}
    return sorted(t for t in pts if t > 0 and all(cd(abs(a - b) * t) >= thr for a, b in combinations(sp, 2)))
for sp in [(1, 2, 3, 4, 5, 6, 7, 16), (1, 2, 3, 4, 5, 16, 64, 720)]:
    g = 0
    for a, b in combinations(sp, 2): g = gcd(g, abs(a - b))
    P = F(1, g)
    iso = instants(sp, F(1, 8), P)
    print(f"{sp}: residues mod 8 {[x % 8 for x in sp]}; gcd of differences {g}; global isolation at 1/8 in (0, {P}]: {[str(t) for t in iso][:12]}{' ...' if len(iso) > 12 else ''} ({len(iso)} points/ends)")
    sub = (0,) + sp
    lon = [t for t in instants(sub, F(1, 9), F(1)) if all(cd(d * t) >= F(1, 9) for d in sp)]
    print(f"   as disparities from a subject at 0 (order 9): lonely instants/ends in (0,1]: {len(lon)}, first {[str(t) for t in lon[:6]]}")
