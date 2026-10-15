#!/usr/bin/env python3
"""Sets with incomplete folded coverage (e in [LO,HI]): compare resonance with e. For each set,
R_e = number of r in R with gcd(r, e) >= 2, and G_max = max over r of gcd(r, e). Reports the
distribution of (R_e, G_max >= 4) among covered and uncovered sets. Exact."""
import sys, math, importlib.util
from itertools import combinations
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
cov = importlib.util.spec_from_file_location("c", "six_folded_coverage_v1.py")
LO, HI = int(sys.argv[1]), int(sys.argv[2])
import fractions
F = fractions.Fraction
def lonely_set(R):
    ivs = [(F(0), F(1))]
    for p in R:
        bands = [(F(6*k + 1, 6*p), F(6*k + 5, 6*p)) for k in range(p)]
        ivs = [(max(a, c), min(b, d)) for a, b in ivs for c, d in bands if max(a, c) <= min(b, d)]
    return ivs
def full(L, e):
    pieces = []
    for a, b in L:
        x, y = a * e, b * e
        if y - x >= 1: return True
        fx = x - (x.numerator // x.denominator); fy = fx + (y - x)
        pieces += [(fx, fy)] if fy <= 1 else [(fx, F(1)), (F(0), fy - 1)]
    pieces.sort(); reach = F(0)
    for a, b in pieces:
        if a > reach: return False
        reach = max(reach, b)
    return reach >= 1
tab = Counter(); ex = []
for e in range(LO, HI + 1):
    for R in combinations(range(1, e), 4):
        S = R + (e,)
        if math.gcd(*S) != 1 or not r.six_residual(S): continue
        f = full(lonely_set(R), e)
        Re = sum(1 for x in R if math.gcd(x, e) >= 2); Gm = max(math.gcd(x, e) for x in R)
        tab[("covered" if f else "UNCOVERED", Re, Gm >= 4)] += 1
        if not f and len(ex) < 12: ex.append((S, [math.gcd(x, e) for x in R]))
for k in sorted(tab): print(" ", k, tab[k])
print("examples (set, gcd(r,e)):", ex)
