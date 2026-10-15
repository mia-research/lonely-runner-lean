#!/usr/bin/env python3
"""Structure of SixResidual (primitive 5-subsets of [1, HI]). Exact integers.
Reports: shape (M = #multiples of 6), which flank classes carry certificates, the least
certificate opening index, cascade move counts, and coverage by candidate framework tools."""
import sys, math, importlib.util
from itertools import combinations
from fractions import Fraction as F
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
N = 6

def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)

def cascade_moves(S, n=N, cap=10000):
    t = F(1, n * min(S)); m = 0
    while m < cap:
        blk = [d for d in S if cd(d * t) < F(1, n)]
        if not blk: return m, t
        nxt = []
        for d in blk:
            x = d * t - F(1, n); c = -((-x.numerator) // x.denominator)
            nxt.append((c + F(1, n)) / d)
        t = max([t] + nxt); m += 1
    return None, t

def cls(S, b):
    tags = []
    if b == max(S): tags.append("largest")
    if b == min(S): tags.append("least")
    if b % 6 == 0: tags.append("mult6")
    if b % 5 == 0: tags.append("mult5")
    if b % 4 == 0: tags.append("mult4")
    return tags

HI = int(sys.argv[1])
shape = Counter(); flank_cls = Counter(); moves = Counter(); total = 0
largest_ok = 0; mult6_ok = 0; mult5_ok = 0; least_ok = 0; grid_ok = Counter()
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    total += 1
    M = sum(1 for d in S if d % 6 == 0)
    shape[M] += 1
    certs = r.certificates(S)
    bs = {b for b, _ in certs}
    largest_ok += max(S) in bs
    least_ok += min(S) in bs
    mult6_ok += any(b % 6 == 0 for b in bs)
    mult5_ok += any(b % 5 == 0 for b in bs)
    m, T = cascade_moves(S)
    moves[m] += 1
    # grid instants a/q (Prop 6.2 form), q <= 30
    for q in range(2, 31):
        if any(all(q <= 6 * ((d * a) % q) <= 5 * q for d in S) for a in range(1, q)):
            grid_ok[q] += 1; break
print(f"HI={HI}: primitive residual sets = {total}")
print("  shape M (multiples of 6):", dict(sorted(shape.items())))
print(f"  certificate at largest flank: {largest_ok}; at least: {least_ok}; at some mult of 6: {mult6_ok}; at some mult of 5: {mult5_ok}")
print("  cascade moves:", dict(sorted(moves.items(), key=lambda kv: (kv[0] is None, kv[0] or 0))))
print("  least q<=30 with a lonely grid instant a/q:", dict(sorted(grid_ok.items())), "none:", total - sum(grid_ok.values()))
