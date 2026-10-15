#!/usr/bin/env python3
"""E31 v2: the same neighbour takeovers, read just BEFORE the death (mover at x - delta, delta = 1e-6 of x, in the
direction opposite to motion), where L and B are both open. J = the four others' common interval (L's laps); count
how many of r's clear bands meet J in positive length (the family L + j e_r standing together), and record the
ratio d_r / max(speeds of J's two bounding runners), plus r's rank among all five speeds.
Usage: six_neighbours_v2.py file.tsv"""
import sys, ast, math
from fractions import Fraction as F
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
fam = Counter(); both = Counter(); ratio = Counter(); fastest = Counter(); n = 0
for row in rows:
    d = ast.literal_eval(row[6]); nz = [(i + 1, v) for i, v in enumerate(d) if v]
    if len(nz) != 1 or abs(nz[0][1]) != 1: continue
    r, s = nz[0]; n += 1
    S = ast.literal_eval(row[0][row[0].index("("):]); m = int(row[1]); x = F(row[2]); L = ast.literal_eval(row[3])
    up = F(S[m - 1]) > S[0] * m
    W = [F(S[i]) if i + 1 > m else F(S[0] * (i + 1)) for i in range(5)]; W[m - 1] = x - (x / 10**6 if up else -x / 10**6)
    others = [i for i in range(1, 6) if i != r]
    ent = {i: (6 * L[i-1] + 1) / (6 * W[i-1]) for i in others}; ext = {i: (6 * L[i-1] + 5) / (6 * W[i-1]) for i in others}
    J0, J1 = max(ent.values()), min(ext.values()); dr = W[r-1]
    if J1 <= J0: both["J empty before the death"] += 1; continue
    k0 = math.floor(J0 * dr - F(5, 6)); cnt = 0; kk = k0
    while (6 * kk + 1) / (6 * dr) < J1:
        lo, hi = max(J0, (6 * kk + 1) / (6 * dr)), min(J1, (6 * kk + 5) / (6 * dr))
        if lo < hi: cnt += 1
        kk += 1
    fam[min(cnt, 8)] += 1
    has = lambda kk: max(J0, (6*kk+1)/(6*dr)) < min(J1, (6*kk+5)/(6*dr))
    both["L and B both open" if has(L[r-1]) and has(L[r-1] + s) else "not both"] += 1
    lo_i = [i for i in others if ent[i] == J0][0]; hi_i = [i for i in others if ext[i] == J1][0]
    ratio[min(round(float(dr / max(W[lo_i-1], W[hi_i-1])), 1), 5.0)] += 1
    fastest["r is the fastest runner" if dr == max(W) else "r not fastest"] += 1
print(f"neighbour takeovers read just before the death: {n}")
print("  ", dict(both))
print("   r's bands meeting J (family size, 8 = 8+):", dict(sorted(fam.items())))
print("   d_r / (faster of J's two bounding runners) (5.0 = 5+):", dict(sorted(ratio.items())))
print("  ", dict(fastest))
