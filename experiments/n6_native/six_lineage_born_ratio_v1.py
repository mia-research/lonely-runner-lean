#!/usr/bin/env python3
"""E30: exact speed ratios of the closing partner and the opening partner to the mover, for every born takeover."""
import sys, ast
from fractions import Fraction as F
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
c = Counter()
for r in rows:
    if r[10] != "born": continue
    S = ast.literal_eval(r[0][r[0].index("("):]); m = int(r[1]); x = F(r[2])
    W = [F(S[i]) if i + 1 > m else F(S[0] * (i + 1)) for i in range(5)]; W[m - 1] = x
    cl = [c_ for c_ in ast.literal_eval(r[4]) if m in c_[:2]]; op = [o for o in ast.literal_eval(r[11]) if m in o[:2]]
    pc = {(c_[1] if c_[0] == m else c_[0]) for c_ in cl}; po = {(o[1] if o[0] == m else o[0]) for o in op}
    c[(tuple(sorted(str(W[p - 1] / x) for p in pc)), tuple(sorted(str(W[p - 1] / x) for p in po)))] += 1
print("born takeovers by (closing partner / mover, opening partner / mover):")
for k, v in c.most_common(): print("  ", v, k)
