#!/usr/bin/env python3
"""Exact cell certificate for §8, v2: as s8_cert_v1, but the starting cells are the unit grid (integer boundaries in
x2..x5, x5 up to X, plus x5 in [X, inf)), so the tight AP point (1,2,3,4,5) is a cell corner (where the spread box
(0,0,0,0,0) and the box (0,1,2,3,4) meet, `grid_tight_pairs`). Bisection as before. Usage: X depth."""
import sys
from fractions import Fraction as F
from collections import Counter
exec(open("s8_cert_v1.py").read().split("start_cells =")[0])
start_cells = []
for a2 in (1, 2):
    for a3 in (1, 2):
        for a4 in range(1, 6):
            for a5 in range(1, int(X)):
                start_cells.append(((F(a2), F(a2 + 1)), (F(a3), F(a3 + 1)), (F(a4), F(a4 + 1)), (F(a5), F(a5 + 1))))
            start_cells.append(((F(a2), F(a2 + 1)), (F(a3), F(a3 + 1)), (F(a4), F(a4 + 1)), (X, None)))
for c in start_cells: run(c, 0)
print(f"X={X}, depth limit {MAXD} (beyond the unit grid): cells visited {ncell}, certified {sum(used.values())}, "
      f"failing {len(fails)}, max depth {maxd}")
for k, n in used.most_common(): print(f"   {n:7d}  {k}")
for c in fails[:25]: print("   FAIL", [(str(a), str(b) if b is not None else 'inf') for a, b in c])
