#!/usr/bin/env python3
"""m4_stall_handoff_v1 -- rule 22 (ii)/(iii) on the 14 STALL boxes of retry3, box by box.

From the centre g of the stalled cell, walk g(eps) = g * (1 + eps * x) along the window-killing
direction x of m4_stall_cone_v1 (topological potentials; boxes whose window graph has a cycle
have no such direction and are reported CYCLIC).  At each consecutive pair of samples where the
clear set jumps (no window of the earlier sample overlaps a window of the later one), bisect to
the jump.  At the jump report the last window before and the first window after, each with its
bounding readings and edges: lower bound e_lo / g_i, upper bound e_hi / g_k.  The handoff is the
SHARED-RATIO type when the two windows are bounded by the same pair {i, k} and
e_hi/e_lo (before) = e_lo'/e_hi' (after) with the roles of i and k exchanged, i.e. the two
windows are complementary half-spaces of one hyperplane g_k / g_i = rho.  Exact Fractions."""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
from m4_fixedpoint_split_v1 import feasible, face, ONE
exec(open('m4_stall_cone_v1.py').read().split('out = []')[0].split('import sys, json')[1])

def edges_of(a, b, g):
    lo = ('one', 1) if a == 1 else min(((abs(a * x - (8 * round((a * x - 1) / 8) + 1)), i, 8 * round((a * x - 1) / 8) + 1) for i, x in enumerate(g)))[1:]
    hi = ('seven', 7) if b == 7 else min(((abs(b * x - (8 * round((b * x - 7) / 8) + 7)), i, 8 * round((b * x - 7) / 8) + 7) for i, x in enumerate(g)))[1:]
    return lo, hi

def S_at(g, x, eps):
    gp = [g[v] * (1 + eps * x[v]) for v in range(7)]; gp[0] = ONE
    return feasible([(y, y) for y in gp]), gp

def overlaps(A, B, tol):
    return any(a1 - tol <= b2 and b1 - tol <= a2 for a1, a2 in A for b1, b2 in B)

rows = []
for l in open('m4_fixedpoint_split_v1_retry3.jsonl'):
    r = json.loads(l)
    if r.get('status') != 'STALL': continue
    n = r['n']; box = [(F(a), F(b)) for a, b in r['box']]
    g = [(a + b) / 2 for a, b in box]
    S = feasible([(y, y) for y in g]) or []
    E = set()
    for a, b in S:
        i = 0 if a == 1 else bounder(a, g, 'lo'); k = 0 if b == 7 else bounder(b, g, 'hi'); E.add((i, k))
    order = topo(list(range(7)), sorted(E))
    if order is None:
        rows.append({"n": n, "type": "CYCLIC"}); print(json.dumps(rows[-1]), flush=True); continue
    pos = {v: p for p, v in enumerate(order)}; x = [F(pos[v] - pos[0]) for v in range(7)]
    faces = [face(v) for v in n]; faces[0] = (ONE, ONE)
    eps_list = [F(1, 2 ** 26) * F(21, 20) ** k for k in range(160)]
    prev = None; found = None
    for e in eps_list:
        Sx, gp = S_at(g, x, e)
        if not all(faces[v][0] <= gp[v] <= faces[v][1] for v in range(7)): break
        if Sx is None: found = ("EMPTY", e); break
        if prev is not None and not overlaps(prev[1], Sx, F(1, 10 ** 7)):
            lo_e, hi_e = prev[0], e
            for _ in range(80):
                mid = (lo_e + hi_e) / 2; Sm, _ = S_at(g, x, mid)
                if Sm is None: break
                if overlaps(prev[1], Sm, F(1, 10 ** 7)): lo_e = mid
                else: hi_e = mid
            Sb, gb = S_at(g, x, lo_e); Sa, ga = S_at(g, x, hi_e)
            wb = min(Sb, key=lambda w: min(abs(w[0] - p[0]) for p in prev[1]))
            wa = Sa[0] if len(Sa) == 1 else min(Sa, key=lambda w: w[1] - w[0])
            found = ("JUMP", float(lo_e), [float(wb[0]), float(wb[1])], edges_of(*wb, gb), [float(wa[0]), float(wa[1])], edges_of(*wa, ga))
            break
        prev = (e, Sx)
    rec = {"n": n, "type": None if found is None else found[0]}
    if found and found[0] == "JUMP":
        _, e, Wb, (blo, bhi), Wa, (alo, ahi) = found
        rec.update({"eps": e, "before": {"R": Wb, "lo": blo, "hi": bhi}, "after": {"R": Wa, "lo": alo, "hi": ahi}})
        if 'one' not in (blo[0], bhi[0], alo[0], ahi[0]) and 'seven' not in (blo[0], bhi[0], alo[0], ahi[0]):
            pair_b = {blo[0], bhi[0]}; pair_a = {alo[0], ahi[0]}
            rho_b = F(bhi[1], blo[1]); rho_a = F(alo[1], ahi[1])
            rec["same_pair"] = pair_b == pair_a and blo[0] == ahi[0]
            rec["rho_before"] = str(rho_b); rec["rho_after"] = str(rho_a)
            rec["shared_ratio"] = bool(rec["same_pair"] and rho_b == rho_a)
    rows.append(rec); print(json.dumps(rec), flush=True)
print(json.dumps({"stall": len(rows), "shared_ratio": sum(1 for r in rows if r.get("shared_ratio")),
                  "cyclic": sum(1 for r in rows if r["type"] == "CYCLIC"),
                  "other": [r["n"] for r in rows if not r.get("shared_ratio") and r["type"] != "CYCLIC"]}))
