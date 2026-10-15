#!/usr/bin/env python3
"""E28: every takeover born at the death point, tested for the 1:5 pair structure: mover m at lap 0, a faster
runner p with d_p = 5x; A closes by (p entering lap 4, m leaving lap 0); B opens by (m entering lap 1, p leaving
lap 5); B's instant = the mover's next entry, 1/3 mover-lap after A's."""
import sys, ast
from fractions import Fraction as F
from collections import Counter
src = open("six_boxes_v1.py").read().split("K = int(sys.argv[1])")[0]
ns = {}; exec(src, ns); alive_interval = ns["alive_interval"]
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
c = Counter(); odd = []
for r in rows:
    S = ast.literal_eval(r[1]); m = int(r[2]); x = F(r[3]); A = ast.literal_eval(r[4]); B = ast.literal_eval(r[8])
    V = [F(S[i]) if i + 1 > m else F(S[0] * (i + 1)) for i in range(5)]
    lo, hi = alive_interval(V, m - 1, B); up = F(S[m - 1]) > S[0] * m
    if (lo < x if up else hi > x): continue
    W = list(V); W[m - 1] = x
    cl = ast.literal_eval(r[7])
    op = [(i+1, j+1, B[i], B[j]) for i in range(5) for j in range(5) if i != j and (6*B[i]+1)*W[j] == (6*B[j]+5)*W[i]]
    ps = [p for (p, mm, kp, km) in cl if mm == m and kp == 4 and km == 0 and W[p-1] == 5 * x]
    ok = any((m, p, 1, 5) in op for p in ps) and x * (F(r[10]) - F(r[6])) == F(1, 3)
    c[ok] += 1
    if not ok: odd.append((S, m, str(x), A, cl, B, op))
print("born at the death point:", sum(c.values()), "; 1:5 pair structure holds:", dict(c))
for o in odd[:10]: print("  other:", o)
