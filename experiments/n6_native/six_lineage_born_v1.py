#!/usr/bin/env python3
"""E30: the 'born' takeovers of the lineage. For each: (i) THIN or not: was any box other than the dying L open on
both sides of the death point (alive at x - eps and x + eps)? (ii) the structure: closing pair of L (involving the
mover) and opening pair of B (involving the mover), as roles (mover leaves/enters, partner, laps), and whether the
partner is the same runner. Speeds at the death: runners above the mover at S, below at the grid, mover at x."""
import sys, ast
from fractions import Fraction as F
from collections import Counter
src = open("six_boxes_v1.py").read().split("K = int(sys.argv[1])")[0]
ns = {}; exec(src, ns); lonely_boxes, instant = ns["lonely_boxes"], ns["instant"]
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
thin = Counter(); struct = Counter(); same_partner = Counter(); examples = []
for r in rows:
    if r[10] != "born": continue
    S = ast.literal_eval(r[0][r[0].index("("):]); m = int(r[1]); x = F(r[2]); L = ast.literal_eval(r[3])
    B = ast.literal_eval(r[5]); tB = F(r[7]) 
    V = [F(S[i]) if i + 1 > m else F(S[0] * (i + 1)) for i in range(5)]
    eps = F(1, 10**9)
    def alive(xx):
        W = list(V); W[m - 1] = xx
        return lonely_boxes(W, max(F(3) / min(W), instant(W, L) + F(2) / min(W)))
    both = (alive(x - eps) & alive(x + eps)) - {L}
    thin["not thin (another box open across x)" if both else "THIN"] += 1
    cl = [c for c in ast.literal_eval(r[4]) if m in c[:2]]; op = [c for c in ast.literal_eval(r[11]) if m in c[:2]]
    def rl(c, kind):
        i, j, ki, kj = c
        return (f"{kind}: mover {'enters' if i == m else 'leaves'} lap {ki if i == m else kj}", f"partner {'leaves' if i == m else 'enters'} lap {kj if i == m else ki}", j if i == m else i)
    for c in cl[:1]:
        for o in op[:1]:
            a, b = rl(c, "close"), rl(o, "open")
            struct[(a[0], a[1], b[0], b[1], "same partner" if a[2] == b[2] else "other partner")] += 1
    if not both and len(examples) < 8: examples.append((S, m, str(x), L, cl, B, op))
print("born takeovers:", sum(thin.values()), dict(thin))
print("structures (closing of L / opening of B):")
for k, v in struct.most_common(12): print("  ", v, k)
for e in examples: print("  THIN example:", e)
