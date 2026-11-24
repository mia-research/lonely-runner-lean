#!/usr/bin/env python3
"""m4_budget_cell_probe_v1 -- for the depth-60 cells of m4_budget_stallcell_v1.jsonl whose
crossing certificate cuts show no 5/3 handoff: (a) does the fixed-instant DFS started AT the
cell terminate (budget 400,000 nodes, depth cap 60 more levels)?  (b) the centre's clear windows
and the readings on edges at each.  Exact Fractions."""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
from m4_fixedpoint_split_v1 import feasible
NONE = [[1,3,4,6,6,7,8],[1,3,4,6,6,8,10],[1,2,4,5,6,7,9],[1,4,5,6,6,8,8],[1,4,5,6,7,8,10]]
def dfs(fc, budget=400000, dcap=60):
    st = [(fc, 0)]; N = L = 0
    while st:
        c, d = st.pop(); N += 1
        if N > budget: return "BUDGET", N, None
        if feasible(c) is not None: L += 1; continue
        if d >= dcap: return "STALL", N, c
        k = max(range(1, 7), key=lambda i: (c[i][1] - c[i][0], -i))
        lo, hi = c[k]; m = (lo + hi) / 2
        a = list(c); a[k] = (lo, m); b = list(c); b[k] = (m, hi); st += [(a, d + 1), (b, d + 1)]
    return "OK", N, None
for l in open('m4_budget_stallcell_v1.jsonl'):
    r = json.loads(l)
    if r['n'] not in NONE: continue
    box = [(F(a), F(b)) for a, b in r['box']]
    g = [(a + b) / 2 for a, b in box]
    S = feasible([(x, x) for x in g]) or []
    wins = []
    for a, b in S:
        on = [(i, float(a * x), float(b * x)) for i, x in enumerate(g) if min(abs(a * x - round(a * x)), abs(b * x - round(b * x))) < F(1, 1000)]
        wins.append({"R": [float(a), float(b)], "near_edge": on})
    st, N, cell = dfs(box)
    rec = {"n": r['n'], "dfs_from_cell": st, "nodes": N, "windows": wins}
    if cell is not None:
        g2 = [(a + b) / 2 for a, b in cell]
        rec["deeper_cell_windows"] = [[float(a), float(b)] for a, b in (feasible([(x, x) for x in g2]) or [])]
        rec["deeper_cell"] = [[str(a), str(b)] for a, b in cell]
    print(json.dumps(rec), flush=True)
