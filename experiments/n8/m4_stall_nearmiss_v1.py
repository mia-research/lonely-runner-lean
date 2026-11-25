#!/usr/bin/env python3
"""m4_stall_nearmiss_v1 -- the depth-140 cell of box (1,2,3,5,6,7,8) (m4_stall_cell_probe_v1.out) lies
outside g*_B = (1,5/2,7/2,875/186,35/6,9625/1426,385/46) on coordinates 5 and 6 (m4_stall_gstar_v1.out).
Does the checker's DFS (m4_stall_cell_probe_v1.dfs: widest of 1..6, lowest index on ties) terminate from it?
Budget 2,000,000 nodes, 100 more levels.  Also: the exact distance of the cell from g*_B per coordinate, in
units of the cell width, and the leaf depths."""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
from collections import Counter
from m4_fixedpoint_split_v1 import feasible
G = [F(1), F(5, 2), F(7, 2), F(875, 186), F(35, 6), F(9625, 1426), F(385, 46)]
for l in open('m4_stall_cell_probe_v1.out'):
    r = json.loads(l)
    if r['n'] == [1, 2, 3, 5, 6, 7, 8]: Q = [(F(a), F(b)) for a, b in r['deeper_cell']]
dist = []
for i in range(7):
    lo, hi = Q[i]; w = hi - lo
    d = 0 if lo <= G[i] <= hi else (lo - G[i] if G[i] < lo else G[i] - hi)
    dist.append([i, str(w), float(d), None if w == 0 else float(d / w)])
print(json.dumps({"distance from gstar per coord [i, width, dist, dist/width]": dist}))
st = [(Q, 0)]; N = 0; depths = Counter(); status = "OK"; maxd = 0
while st:
    c, d = st.pop(); N += 1
    if N > 2000000: status = "BUDGET"; break
    if feasible(c) is not None: depths[d] += 1; continue
    if d >= 100: status = "STALL"; break
    maxd = max(maxd, d)
    k = max(range(1, 7), key=lambda i: (c[i][1] - c[i][0], -i))
    lo, hi = c[k]; m = (lo + hi) / 2
    a = list(c); a[k] = (lo, m); b = list(c); b[k] = (m, hi); st += [(a, d + 1), (b, d + 1)]
print(json.dumps({"status": status, "nodes": N, "leaves": sum(depths.values()), "leaf depths": dict(sorted(depths.items())), "max internal depth": maxd}))
