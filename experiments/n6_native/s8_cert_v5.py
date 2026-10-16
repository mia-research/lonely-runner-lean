#!/usr/bin/env python3
"""Exact cell certificate for §8, v5: the final list of s8_cert_v4 (fixed, no rounds), run once, with every certified
leaf exported (cell intervals and the statement) to s8_cert_v5_leaves.txt, and every split recorded so the tree can be
re-walked. Usage: X depth."""
import sys, math
from fractions import Fraction as F
from collections import Counter
exec(open("s8_cert_v3.py").read().split("exec(\"start_cells = []\"")[0])
W3[:] = [(0, 0, 0), (1, 2, 3), (0, 1, 1), (0, 0, 1), (0, 1, 2), (2, 6, 7), (1, 3, 4)]
EXTRA[:] = [(0, 1, 2, 3, 9), (2, 6, 7, 10, 14), (1, 3, 4, 6, 17), (1, 3, 4, 6, 18), (0, 1, 1, 2, 6)]
leaves = []
def run2(c, d):
    c = clip(c)
    if c is None: return 0
    r = certify(c)
    if r: leaves.append((c, r)); return 1
    if d >= MAXD: raise SystemExit(f"FAIL {c}")
    widths = [(c[i][1] - c[i][0]) if c[i][1] is not None else F(-1) for i in range(4)]
    i = max(range(4), key=lambda j: widths[j]); a, b = c[i]; mid = (a + b) / 2
    return run2(c[:i] + ((a, mid),) + c[i + 1:], d + 1) + run2(c[:i] + ((mid, b),) + c[i + 1:], d + 1)
starts = []
for a2 in (1, 2):
    for a3 in (1, 2):
        for a4 in range(1, 6):
            for a5 in range(1, int(X)):
                starts.append(((F(a2), F(a2 + 1)), (F(a3), F(a3 + 1)), (F(a4), F(a4 + 1)), (F(a5), F(a5 + 1))))
            starts.append(((F(a2), F(a2 + 1)), (F(a3), F(a3 + 1)), (F(a4), F(a4 + 1)), (X, None)))
n = sum(run2(c, 0) for c in starts)
with open("s8_cert_v5_leaves.txt", "w") as f:
    for c, r in leaves:
        f.write(" ".join(f"{a} {b if b is not None else 'inf'}" for a, b in c) + f" | {r[0]} {','.join(map(str, r[1]))}\n")
print(f"X={X}: certified leaves {n}; statements used:", Counter((r[0], r[1]) for _, r in leaves).most_common())
print("largest denominator in a cell endpoint:", max(x.denominator for c, _ in leaves for p in c for x in p if x is not None))
