#!/usr/bin/env python3
"""(A) at the tight sets: list the lonely points in [0,1) with the runners on edges (entering: reading k+1/6;
leaving: reading k+5/6), then random small perturbations of all five speeds: which points open into a positive
interval. Prediction to test: at each point one entering runner e and one leaving runner l, and the point opens iff
the entry precedes the exit, i.e. (6k_e+1) d_l < (6k_l+5) d_e."""
import random, sys
from fractions import Fraction as F
from collections import Counter
s6 = F(1, 6)
def floor(x): return x.numerator // x.denominator
def ivs(V, lo, hi):
    out = [(lo, hi)]
    for v in V:
        new = []
        for a, b in out:
            k = max(floor(a * v - s6) - 1, 0)
            while True:
                l, r = (k + s6) / v, (k + 5 * s6) / v
                if l > b: break
                L, R = max(a, l), min(b, r)
                if L <= R: new.append((L, R))
                k += 1
        out = new
    return out
rng = random.Random(11)
for S in ((1, 2, 3, 4, 5), (1, 3, 4, 5, 9)):
    c = 12; G = [F(c * s) for s in S]
    pts = [a for a, b in ivs(G, F(0), F(1, c) - F(1, 10**9))]
    print(f"== {S} (scaled by {c}): lonely points in one period:", [str(p * c) + "/c" for p in pts])
    rules = []
    for p in pts:
        rd = [g * p for g in G]
        ent = [(i, floor(r)) for i, r in enumerate(rd) if r - floor(r) == s6]
        lev = [(i, floor(r)) for i, r in enumerate(rd) if r - floor(r) == 5 * s6]
        print(f"   t = {p*c}/c: readings {[str(r) for r in rd]}; entering {[(i+1,k) for i,k in ent]}; leaving {[(i+1,k) for i,k in lev]}")
        rules.append((ent, lev))
    pat = Counter(); mism = 0; nopen = 0; trials = 0
    for _ in range(3000):
        V = [g + F(rng.randint(-1000, 1000), 10**6) for g in G]
        trials += 1; opened = []
        for p, (ent, lev) in zip(pts, rules):
            d = F(1, 500 * c)
            has = any(b > a for a, b in ivs(V, p - d, p + d))
            pred = all((6*ke+1)*V[l] < (6*kl+5)*V[e] for e, ke in ent for l, kl in lev)
            mism += has != pred; opened.append(has)
        pat[tuple(opened)] += 1; nopen += not any(opened)
    print(f"   perturbations {trials}; rule mismatches {mism}; perturbations with no point opening {nopen}")
    print("   opening patterns:", dict(pat))
