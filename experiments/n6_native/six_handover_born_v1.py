#!/usr/bin/env python3
"""E28: the takeovers born exactly at the death point. For each: A, B, the closing pair of A and the opening pair
of B (B's pair inequality that is tight at x: the pair that just became satisfiable), and B's instant against A's."""
import sys, ast
from fractions import Fraction as F
src = open("six_boxes_v1.py").read().split("K = int(sys.argv[1])")[0]
ns = {}; exec(src, ns); alive_interval = ns["alive_interval"]
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
n = 0
for r in rows:
    S = ast.literal_eval(r[1]); m = int(r[2]); x = F(r[3]); A = ast.literal_eval(r[4]); B = ast.literal_eval(r[8])
    V = [F(S[i]) if i + 1 > m else F(S[0] * (i + 1)) for i in range(5)]
    lo, hi = alive_interval(V, m - 1, B); up = F(S[m - 1]) > S[0] * m
    if (lo < x if up else hi > x): continue
    W = list(V); W[m - 1] = x
    opening = [(i+1, j+1, B[i], B[j]) for i in range(5) for j in range(5) if i != j and (6*B[i]+1)*W[j] == (6*B[j]+5)*W[i]]
    n += 1
    if n <= 15: print(r[0], S, "mover", m, "x", x, "A", A, "closing", r[7], "| B", B, "opening pair", opening, "| tA", r[6], "tB", r[10])
print("born at the death point:", n)
