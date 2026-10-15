#!/usr/bin/env python3
"""Positive control for six_boxes_v1.py: (a) the grid point at the start of the first move must be reported
degenerate; (b) a path moving d5 from 4c to 6c with the others at the grid must report a degenerate point at d5 = 5c;
(c) junction configurations (ends of moves) on the sample paths: are any degenerate?"""
import sys, importlib.util
from fractions import Fraction as F
spec = importlib.util.spec_from_file_location("bx", "six_boxes_v1.py")
src = open("six_boxes_v1.py").read().split("K = int(sys.argv[1])")[0]
ns = {}; exec(src, ns)
move = ns["move"]
c = F(7)
V = [c * k for k in range(1, 6)]
print("(a) grid, move d5 5c -> 8c:", [(str(x), [(z[0], str(z[1]), z[2]) for z in al]) for x, al in move(list(V), 4, 8 * c) if x == 5 * c])
W = list(V); W[4] = 4 * c
print("(b) d5 4c -> 6c:", [(str(x), [(z[0], str(z[1]), z[2]) for z in al]) for x, al in move(W, 4, 6 * c)])
sets = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]][::8]
junc = 0; jdeg = 0
for S in sets:
    V = [F(S[0] * k) for k in range(1, 6)]
    for m in (4, 3, 2, 1):
        b = F(S[m])
        if V[m] != b:
            res = move(list(V), m, b)
            junc += 1; jdeg += any(x == b for x, _ in res)
        V[m] = b
print(f"(c) junctions {junc}; degenerate {jdeg}")
