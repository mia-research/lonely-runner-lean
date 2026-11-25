#!/usr/bin/env python3
"""m4_wide_blocked_v3 -- BLOCKED points (m4_stall_gstar_v1's lemma) in the three wide BUDGET boxes, found with an LP
to steer and checked exactly.  Cells: 150 non-leaf cells at depth 48 per box, reached by descents of the retry3
checker (pin 0, widest of 1..6, lowest index on ties) that pick a non-leaf child by a seeded generator (the seed only
chooses which cells are looked at; nothing below depends on it).  In each cell: the clear windows at the centre with the
nearest reading edge at each end; the hyperplanes (8j+1) g_k = (8j'+7) g_i of the windows bounded at both ends; an LP
(scipy, floats: STEERING ONLY) for a point of the cell on all of them, as far from the faces as possible.  If the LP is
feasible, the free coordinates of the exact solution are set to the LP point's values rounded to rationals inside the
cell, the pivots solved exactly in Fractions, and the point checked exactly (m4_wide_blocked_v2.check: in the cell, C(g*)
finite, every point killed consistently).  Also run on the two STALL boxes of item 2 as a check that the search finds
their points.  Output per box: cells, LP-feasible, verified, the dimension 6 - rank of the verified points' hyperplanes,
and the first verified point with its C(g*)."""
import sys, json, random
sys.path.insert(0, '.')
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import numpy as np
from scipy.optimize import linprog
from m4_fixedpoint_split_v1 import feasible, face, ONE
from m4_wide_blocked_v2 import kids, nearest_edges, check

def rows_of(Q):
    g = [(a + b) / 2 for a, b in Q]
    S = feasible([(x, x) for x in g]) or []
    rows = []
    for lo, hi in nearest_edges(g, S):
        if lo and hi:
            (i, el), (k, eh) = lo, hi
            r = [F(0)] * 7; r[k] += el; r[i] -= eh
            if any(r): rows.append(r)
    return rows

def exact_solve(rows, free_vals):
    A = [[r[j] for j in range(1, 7)] + [-r[0]] for r in rows]
    piv = []; m = 0
    for col in range(6):
        p = next((r for r in range(m, len(A)) if A[r][col] != 0), None)
        if p is None: continue
        A[m], A[p] = A[p], A[m]
        A[m] = [x / A[m][col] for x in A[m]]
        for r in range(len(A)):
            if r != m and A[r][col] != 0:
                f = A[r][col]; A[r] = [x - f * y for x, y in zip(A[r], A[m])]
        piv.append(col); m += 1
    if any(all(x == 0 for x in row[:6]) and row[6] != 0 for row in A): return None, None
    x = [None] * 6
    for col in range(6):
        if col not in piv: x[col] = free_vals[col]
    for r, col in enumerate(piv):
        x[col] = A[r][6] - sum(A[r][c] * x[c] for c in range(6) if c not in piv)
    return [F(1)] + x, 6 - len(piv)

def try_cell(Q):
    rows = rows_of(Q)
    if not rows: return {"lp": False, "ok": False, "why": "no closed-window hyperplane"}
    # variables g1..g6, t ; maximise t
    A_eq = [[float(r[j]) for j in range(1, 7)] + [0.0] for r in rows]; b_eq = [-float(r[0]) for r in rows]
    A_ub = []; b_ub = []
    sc = float(Q[1][1] - Q[1][0]) or 1.0
    for i in range(1, 7):
        lo, hi = float(Q[i][0]), float(Q[i][1])
        e = [0.0] * 7; e[i - 1] = -1.0; e[6] = 1.0; A_ub.append(e); b_ub.append(-lo)      # lo + t <= g
        e = [0.0] * 7; e[i - 1] = 1.0; e[6] = 1.0; A_ub.append(e); b_ub.append(hi)        # g + t <= hi
    res = linprog([0] * 6 + [-1.0], A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(None, None)] * 6 + [(-1, 1)], method='highs')
    if res.status != 0 or res.x[6] < -1e-12: return {"lp": False, "ok": False, "why": "lp infeasible"}
    fv = []
    for i in range(6):
        lo, hi = Q[i + 1]
        v = F(res.x[i]).limit_denominator(10 ** 15)
        fv.append(min(max(v, lo), hi))
    g, dim = exact_solve(rows, fv)
    if g is None: return {"lp": True, "ok": False, "why": "inconsistent"}
    if any(v <= 0 for v in g): return {"lp": True, "ok": False, "why": "nonpositive"}
    ok, info = check(g, Q)
    return {"lp": True, "ok": ok, "why": info, "dim": dim, "gstar": [str(v) for v in g]}

def deep_cells(n, depth, count, seed):
    rnd = random.Random(seed)
    faces = [face(v) for v in n]; faces[0] = (ONE, ONE)
    out = []; tries = 0
    while len(out) < count and tries < 20 * count:
        tries += 1; c = faces; ok = True
        for d in range(depth):
            r = kids(c)
            if r is None: ok = False; break
            ch = [x for x in r if feasible(x) is None]
            if not ch: ok = False; break
            c = rnd.choice(ch)
        if ok: out.append(c)
    return out, tries

if __name__ == "__main__":
    boxes = [[1, 3, 4, 5, 6, 7, 13], [1, 3, 4, 5, 6, 7, 14], [1, 4, 5, 6, 6, 8, 15], [1, 3, 4, 5, 5, 7, 15], [1, 2, 3, 5, 6, 7, 8]]
    with Pool(4) as pool:
        for n in boxes:
            cells, tries = deep_cells(n, 48, 150, 20261125)
            out = pool.map(try_cell, cells)
            ver = [o for o in out if o["ok"]]
            print(json.dumps({"n": n, "depth": 48, "cells": len(cells), "descents": tries,
                              "lp_feasible": sum(o["lp"] for o in out), "verified": len(ver),
                              "dims_verified": dict(Counter(o["dim"] for o in ver)),
                              "fail_reasons": dict(Counter(str(o["why"])[:30] for o in out if not o["ok"])),
                              "first_verified": ver[0] if ver else None}), flush=True)
