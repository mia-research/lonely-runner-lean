#!/usr/bin/env python3
"""m4_stall_limit_v1 -- E925 item 5(iii): the two cells that reach the cap again, (1,3,4,5,5,7,15) and
(1,2,3,5,6,7,8).  Follow the fixed-instant checker's own descent (m4_stall_cell_probe_v1.dfs rule:
bisect the widest of coordinates 1..6, lowest index on ties, depth-first, second half pushed last)
along the FIRST failing branch, to depth D.  At the deepest cell's centre, read each clear window's
bounding edges exactly: lower = (8j+1)/g_i or 1, upper = (8j'+7)/g_k or 7.  A window that shrinks to a
point gives the hyperplane (8j+1) g_k = (8j'+7) g_i.  Solve these with the pin g_0 = 1 for the limit
point g*, exactly.  Then test, exactly:
  (a) g* lies in every cell of the branch (closed);
  (b) the clear set of R at g* (feasible on point faces) is a finite set of single points;
  (c) for each such point R0, which readings bound it at g* (low edge reading i, high edge reading k);
  (d) whether g*_i and g*_k are dyadic rationals (every face of every checker cell is dyadic, since the
      box faces are half-integers and cuts are midpoints).
Lemma used [P, derivation in the log entry]: a cell Q containing g* has a fixed clear R only if R is a
point of the clear set at g*, and for R0 bounded below by reading i and above by reading k this needs
lo_i(Q) = g*_i and hi_k(Q) = g*_k.  If for every R0 one of those coordinates is non-dyadic, no cell
containing g* is ever a leaf, so the descent does not terminate."""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
from m4_fixedpoint_split_v1 import feasible, face
import sympy

def descend(fc, D):
    """first failing branch of the checker from cell fc, to depth D; returns list of cells."""
    path = [fc]
    c = fc
    for d in range(D):
        if feasible(c) is not None:
            return path, 'LEAF'
        k = max(range(1, 7), key=lambda i: (c[i][1] - c[i][0], -i))
        lo, hi = c[k]; m = (lo + hi) / 2
        a = list(c); a[k] = (lo, m); b = list(c); b[k] = (m, hi)
        # the checker pops b first (pushed last); take b if it fails, else a
        nxt = b if feasible(b) is None else a
        if feasible(nxt) is not None:
            return path + [nxt], 'BOTH_CHILDREN_LEAVES'
        path.append(nxt); c = nxt
    return path, 'DEPTH'

def edges_at(g, S):
    out = []
    for a, b in S:
        lo = None; hi = None
        for i, x in enumerate(g):
            y = a * x
            if y.denominator == 1 and y % 8 == 1: lo = (i, int(y))
            y2 = b * x
            if y2.denominator == 1 and y2 % 8 == 7: hi = (i, int(y2))
        out.append((a, b, lo, hi))
    return out

def nearest_edges(g, S):
    """at a non-limit centre: the reading whose edge is closest to each window end."""
    out = []
    for a, b in S:
        best_lo = min(((abs(a * x - (8 * ((a * x - 1) // 8) + 1)), i, 8 * int((a * x - 1) // 8) + 1) for i, x in enumerate(g)), default=None)
        best_hi = min(((abs(b * x - (8 * ((b * x + 1) // 8) - 1)), i, 8 * int((b * x + 1) // 8) - 1) for i, x in enumerate(g)), default=None)
        lo = None if a == 1 else (best_lo[1], best_lo[2])
        hi = None if b == 7 else (best_hi[1], best_hi[2])
        out.append((a, b, lo, hi))
    return out

def dyadic(x):
    d = F(x).denominator
    return d & (d - 1) == 0

BOXES = [[1, 3, 4, 5, 5, 7, 15], [1, 2, 3, 5, 6, 7, 8]]
retry = {tuple(json.loads(l)['n']): json.loads(l) for l in open('m4_fixedpoint_split_v1_retry3.jsonl')}
for n in BOXES:
    r = retry[tuple(n)]
    cell = [(F(a), F(b)) for a, b in r['box']]
    path, why = descend(cell, 200)
    c = path[-1]
    g = [(a + b) / 2 for a, b in c]
    S = feasible([(x, x) for x in g]) or []
    W = nearest_edges(g, S)
    # hyperplanes from windows bounded by two readings
    gs = sympy.symbols('g0:7')
    eqs = [sympy.Eq(gs[0], 1)]
    for a, b, lo, hi in W:
        if lo and hi:
            (i, el), (k, eh) = lo, hi
            eqs.append(sympy.Eq(el * gs[k], eh * gs[i]))
    # coordinates pinned at a face of the box on the branch (cell hi or lo equals the box face)
    bf = [face(v) for v in n]; bf[0] = (F(1), F(1))
    for i in range(1, 7):
        if c[i][1] == bf[i][1]: eqs.append(sympy.Eq(gs[i], sympy.Rational(bf[i][1].numerator, bf[i][1].denominator)))
        elif c[i][0] == bf[i][0]: eqs.append(sympy.Eq(gs[i], sympy.Rational(bf[i][0].numerator, bf[i][0].denominator)))
    sol = sympy.solve(eqs, gs, dict=True)
    rec = {"n": n, "depth_followed": len(path) - 1, "stop": why,
           "windows_at_centre": [[str(a), str(b), lo, hi] for a, b, lo, hi in W],
           "constraints": [str(e) for e in eqs], "solutions": len(sol)}
    if len(sol) == 1 and all(gs[i] in sol[0] for i in range(7)) and all(sol[0][gs[i]].is_Rational for i in range(7)):
        gstar = [F(int(sympy.fraction(sol[0][gs[i]])[0]), int(sympy.fraction(sol[0][gs[i]])[1])) for i in range(7)]
        rec["gstar"] = [str(x) for x in gstar]
        rec["(a) gstar in every branch cell"] = all(all(cc[i][0] <= gstar[i] <= cc[i][1] for i in range(7)) for cc in path)
        Sg = feasible([(x, x) for x in gstar]) or []
        rec["(b) clear set at gstar"] = [[str(a), str(b)] for a, b in Sg]
        rec["(b) all single points"] = all(a == b for a, b in Sg)
        E = edges_at(gstar, Sg)
        rec["(c) bounding readings"] = [[str(a), lo, hi] for a, b, lo, hi in E]
        rec["(d) dyadic coords"] = [dyadic(x) for x in gstar]
        blocked = []
        for a, b, lo, hi in E:
            need = []
            if lo: need.append(lo[0])
            if hi: need.append(hi[0])
            blocked.append(any(not dyadic(gstar[i]) for i in need))
        rec["(d) every point blocked by a non-dyadic coordinate"] = bool(E) and all(blocked)
        rec["per-point blocked"] = blocked
    else:
        rec["sol"] = str(sol)
    print(json.dumps(rec), flush=True)
