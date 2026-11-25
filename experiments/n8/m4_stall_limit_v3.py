#!/usr/bin/env python3
"""m4_stall_limit_v3 -- v2 with the free-coordinate step fixed: only the PARAMETERS of the solution
(symbols left free by the hyperplanes) are set to a cell endpoint, never a coordinate expressed through them.
Otherwise as m4_stall_limit_v1, on all 14 depth-80 STALL cells of retry3 and the two
deeper cells of m4_stall_cell_probe_v1 (depth 140).  No descent is followed: at the cell centre, each
clear window is read with the reading whose edge is nearest each end; a window bounded by two readings
gives the hyperplane (8j+1) g_k = (8j'+7) g_i.  With the pin g_0 = 1, coordinates the hyperplanes leave
free are set to the endpoint of the cell with the smaller denominator (then checked).  Exact tests at the
candidate g*:  (a) g* in the cell (closed); (b) the clear set C(g*) of R in [1,7], and whether every
component is a single point; (c) the readings bounding each point; (d) BLOCKED = every point of C(g*) has
a bounding reading with a non-dyadic coordinate.
Lemma [P]: if g* lies in a cell Q of the checker and is BLOCKED, Q is not a leaf.  (R fixed for Q puts R in
C(g*); a point R0 bounded below by reading i needs lo_i(Q) >= g*_i, so lo_i(Q) = g*_i; above by reading k
needs hi_k(Q) = g*_k; cell faces are dyadic, since box faces are half-integers and cuts are midpoints.)
Each child of a cell containing g* that contains g* is again not a leaf, and at least one child contains it,
so the descent from Q has an infinite branch, whatever the cut order."""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
from m4_fixedpoint_split_v1 import feasible
import sympy

def nearest_edges(g, S):
    out = []
    for a, b in S:
        lo = None if a == 1 else min(((abs(a * x - (8 * ((a * x - 1) // 8) + 1)), i, 8 * int((a * x - 1) // 8) + 1) for i, x in enumerate(g)))[1:]
        hi = None if b == 7 else min(((abs(b * x - (8 * ((b * x + 1) // 8) - 1)), i, 8 * int((b * x + 1) // 8) - 1) for i, x in enumerate(g)))[1:]
        out.append((a, b, lo, hi))
    return out

def edges_at(g, S):
    out = []
    for a, b in S:
        los = [(i, int(a * x)) for i, x in enumerate(g) if (a * x).denominator == 1 and int(a * x) % 8 == 1]
        his = [(i, int(b * x)) for i, x in enumerate(g) if (b * x).denominator == 1 and int(b * x) % 8 == 7]
        out.append((a, b, los, his))
    return out

def dyadic(x):
    d = F(x).denominator
    return d & (d - 1) == 0

def analyse(n, cell, label):
    g = [(a + b) / 2 for a, b in cell]
    S = feasible([(x, x) for x in g]) or []
    W = nearest_edges(g, S)
    gs = sympy.symbols('g0:7')
    eqs = [sympy.Eq(gs[0], 1)]
    for a, b, lo, hi in W:
        if lo and hi:
            (i, el), (k, eh) = lo, hi
            eqs.append(sympy.Eq(el * gs[k], eh * gs[i]))
    rec = {"n": n, "cell": label, "windows_at_centre": [[float(a), float(b), lo, hi] for a, b, lo, hi in W]}
    sol = sympy.solve(eqs, gs, dict=True)
    if len(sol) != 1:
        rec["solve"] = "solutions=%d" % len(sol); return rec
    s = sol[0]
    params = set(x for x in gs if x not in s)
    for v_ in s.values(): params |= v_.free_symbols
    free = sorted(gs.index(x) for x in params)
    for i in free:
        lo, hi = cell[i]
        v = lo if lo.denominator <= hi.denominator else hi
        eqs.append(sympy.Eq(gs[i], sympy.Rational(v.numerator, v.denominator)))
        s2 = sympy.solve(eqs, gs, dict=True)
        if len(s2) == 1: s = s2[0]
    if any(gs[i] not in s or s[gs[i]].free_symbols for i in range(7)):
        rec["solve"] = "underdetermined"; return rec
    gstar = [F(int(sympy.fraction(s[gs[i]])[0]), int(sympy.fraction(s[gs[i]])[1])) for i in range(7)]
    rec["pinned_free"] = free
    rec["gstar"] = [str(x) for x in gstar]
    rec["(a) in cell"] = all(cell[i][0] <= gstar[i] <= cell[i][1] for i in range(7))
    Sg = feasible([(x, x) for x in gstar]) or []
    rec["(b) C(gstar)"] = [[str(a), str(b)] for a, b in Sg]
    rec["(b) all single points"] = bool(Sg) and all(a == b for a, b in Sg)
    E = edges_at(gstar, Sg)
    rec["(c) bounding"] = [[str(a), los, his] for a, b, los, his in E]
    rec["(d) dyadic"] = [dyadic(x) for x in gstar]
    blk = [a == b and any(not dyadic(gstar[i]) for i, _ in los + his) for a, b, los, his in E]
    rec["(d) per point blocked"] = blk
    rec["BLOCKED"] = bool(E) and all(blk)
    rec["LEMMA APPLIES (in cell and BLOCKED)"] = rec["(a) in cell"] and rec["BLOCKED"]
    return rec

for l in open('m4_fixedpoint_split_v1_retry3.jsonl'):
    r = json.loads(l)
    if r.get('status') != 'STALL': continue
    print(json.dumps(analyse(r['n'], [(F(a), F(b)) for a, b in r['box']], 'depth80')), flush=True)
for l in open('m4_stall_cell_probe_v1.out'):
    r = json.loads(l)
    if 'deeper_cell' in r:
        print(json.dumps(analyse(r['n'], [(F(a), F(b)) for a, b in r['deeper_cell']], 'depth140')), flush=True)
