#!/usr/bin/env python3
"""Observation. Worst case over M for the failing cells (s6_rest_v6): the sum lemma's interval
I = [1/3 + v3/(3 v5), (5/6)(1 - v1/v3)] and the meeting fold's runner-5 condition v5 |W| >= 1/3 both get harder as v5
decreases, so v5 = v4 (M = 1/3, the closed limit) is the worst point of the cell. Per cell and v1 (= a mod D, v1 < v3/3,
v1 < v2): does the sum lemma (v4 = v3 + v1 only) or the meeting fold close at v5 = v4? If yes, every v5 > v4, integer or
not, is closed by the same window -- this covers the g | v4 reductions (v5/g rational) too."""
import ast
from fractions import Fraction as F
from collections import Counter
from s6_rest_v1 import sum_ok, meet_fold
cells = []
for line in open("s6_rest_v6.out"):
    if line.startswith("   ("): cells.append(ast.literal_eval(line.strip().split(" M in ")[0]))
res = Counter(); bad = []
for D, c, d, a, lam in cells:
    v2, v3 = c * D, (c + 1) * D; v4 = v3 + d
    for v1 in range(a, v2, D):
        if 3 * v1 >= v3: continue
        S = (v1, v2, v3, v4, v4)   # v5 = v4: the worst M
        how = "sum" if sum_ok(S) else "meeting fold" if meet_fold(S) else "NOT at M = 1/3"
        res[how] += 1
        if how.startswith("NOT"): bad.append((D, c, d, v1))
print(f"cells x v1: {sum(res.values())}: {dict(res)}; open at M = 1/3: {bad}")
