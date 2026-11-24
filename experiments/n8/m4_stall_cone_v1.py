#!/usr/bin/env python3
"""m4_stall_cone_v1 -- rule 22 (ii) on the STALL cells.  At the cell centre g each clear window
[Rlo,Rhi] is bounded below by reading i's exit edge e_lo/g_i (or R=1) and above by reading k's
entry edge e_hi/g_k (or R=7).  In log-coordinates x_r = dg_r/g_r the window dies, to first
order, iff x_k > x_i ('one' and 'seven' and the pin are the node 0 with x_0 = 0).  A direction
killing EVERY window exists iff that directed graph is acyclic.  If it is, step g along the
topological-order direction (exact Fractions, staying inside the box faces of n) and test
feasible() on the point: None = a reading vector of the box with no clear R in [1,7], i.e.
NoCarve fails there.  Output per stall box: edges, acyclic?, and the outcome of the search."""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
from m4_fixedpoint_split_v1 import feasible, face, ONE

def bounder(R, g, kind):
    best = None
    for i, x in enumerate(g):
        v = R * x
        e = (8 * round((v - 1) / 8) + 1) if kind == 'lo' else (8 * round((v - 7) / 8) + 7)
        d = abs(v - e)
        if best is None or d < best[0]: best = (d, i, e)
    return best[1]

def topo(nodes, edges):
    indeg = {v: 0 for v in nodes}
    for a, b in edges: indeg[b] += 1
    order = []; Q = [v for v in nodes if indeg[v] == 0]
    while Q:
        v = Q.pop(); order.append(v)
        for a, b in edges:
            if a == v:
                indeg[b] -= 1
                if indeg[b] == 0: Q.append(b)
    return order if len(order) == len(nodes) else None

out = []
for l in open('m4_fixedpoint_split_v1_retry3.jsonl'):
    r = json.loads(l)
    if r.get('status') != 'STALL': continue
    n = r['n']; box = [(F(a), F(b)) for a, b in r['box']]
    g = [(a + b) / 2 for a, b in box]
    S = feasible([(x, x) for x in g]) or []
    edges = set()
    for a, b in S:
        i = 0 if a == 1 else bounder(a, g, 'lo')
        k = 0 if b == 7 else bounder(b, g, 'hi')
        edges.add((i, k))
    order = topo(list(range(7)), sorted(edges))
    rec = {"n": n, "edges": sorted(edges), "acyclic": order is not None}
    if order is not None:
        # potentials: x_v = position in topological order, shifted so x_0 = 0
        pos = {v: p for p, v in enumerate(order)}
        x = [F(pos[v] - pos[0]) for v in range(7)]
        faces = [face(v) for v in n]; faces[0] = (ONE, ONE)
        found = None
        eps = F(1, 2 ** 40)
        while eps < F(1, 4) and found is None:
            gp = [g[v] * (1 + eps * x[v]) for v in range(7)]
            gp[0] = ONE
            inside = all(faces[v][0] <= gp[v] <= faces[v][1] for v in range(7))
            if inside and feasible([(y, y) for y in gp]) is None:
                found = gp
            eps *= 2
        rec["no_clear_point"] = None if found is None else [str(y) for y in found]
        rec["eps"] = None if found is None else str(eps / 2)
    out.append(rec); print(json.dumps(rec), flush=True)
print(json.dumps({"stall": len(out), "acyclic": sum(o['acyclic'] for o in out),
                  "no_clear_found": sum(1 for o in out if o.get('no_clear_point'))}))
