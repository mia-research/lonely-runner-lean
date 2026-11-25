#!/usr/bin/env python3
"""m4_stall_gstar_v1 -- E925 item 5(iii), the two boxes whose cells reach the cap again.  Exact check of
the explicit limit points found by m4_stall_limit_v1..v3:
  A = (1, 119/39, 155/38, 11/2, 1023/206, 7, 31/2)        box (1,3,4,5,5,7,15)
  B = (1, 5/2, 7/2, 875/186, 35/6, 9625/1426, 385/46)    box (1,2,3,5,6,7,8)
Lemma [P].  Let Q be a checker cell containing g*.  If Q has a fixed clear R, then R is in C(g*), the clear
set at g*; if C(g*) is finite, R = R0 is one of its points, and for every reading i bounding R0 from below
(R0 g*_i = 8j+1) Q needs lo_i(Q) = g*_i, and for every reading k bounding it from above (R0 g*_k = 8j'+7, or
R0 = 7 with k = the bound 7) Q needs hi_k(Q) = g*_k.  Call R0 KILLED in Q when one of these equalities fails
strictly.  If every point of C(g*) is killed in Q, Q is not a leaf.  A strict inequality lo_i < g*_i survives
into the child that contains g*: a cut at m != g*_i leaves one such child, with lo_i unchanged or m < g*_i;
a cut at m = g*_i (possible only if g*_i is dyadic, all cell faces being dyadic) leaves two, and the lower one
keeps it.  The same holds for hi_k > g*_k with the upper child.  So if, in Q, each point of C(g*) is killed by
a witness, and no dyadic coordinate serves as a lower witness for one point and an upper witness for another,
then some branch from Q has every cell non-leaf: the checker's descent from Q does not terminate, whatever the
order of cuts.  Checked here exactly, per point: its bounding readings, a witness, strictness in Q, the
consistency condition."""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
from m4_fixedpoint_split_v1 import feasible, face

def dyadic(x):
    d = F(x).denominator
    return d & (d - 1) == 0

PTS = {(1, 3, 4, 5, 5, 7, 15): [F(1), F(119, 39), F(155, 38), F(11, 2), F(1023, 206), F(7), F(31, 2)],
       (1, 2, 3, 5, 6, 7, 8): [F(1), F(5, 2), F(7, 2), F(875, 186), F(35, 6), F(9625, 1426), F(385, 46)]}
cells = {}
for l in open('m4_fixedpoint_split_v1_retry3.jsonl'):
    r = json.loads(l)
    if tuple(r['n']) in PTS and r.get('status') == 'STALL':
        cells[(tuple(r['n']), 'depth80')] = [(F(a), F(b)) for a, b in r['box']]
for l in open('m4_stall_cell_probe_v1.out'):
    r = json.loads(l)
    if tuple(r['n']) in PTS and 'deeper_cell' in r:
        cells[(tuple(r['n']), 'depth140')] = [(F(a), F(b)) for a, b in r['deeper_cell']]
for n, g in PTS.items():
    box = [face(v) for v in n]; box[0] = (F(1), F(1))
    out = {"n": list(n), "gstar": [str(x) for x in g],
           "in box": all(box[i][0] <= g[i] <= box[i][1] for i in range(7)),
           "pin g0 = 1": g[0] == 1, "dyadic": [dyadic(x) for x in g]}
    C = feasible([(x, x) for x in g]) or []
    out["C(gstar)"] = [[str(a), str(b)] for a, b in C]
    out["C finite (all single points)"] = bool(C) and all(a == b for a, b in C)
    pts = []
    for a, b in C:
        R = a
        los = [i for i, x in enumerate(g) if (R * x).denominator == 1 and int(R * x) % 8 == 1]
        his = [i for i, x in enumerate(g) if (R * x).denominator == 1 and int(R * x) % 8 == 7]
        pts.append({"R": str(R), "lower": los, "upper": his, "upper_is_7": R == 7, "lower_is_1": R == 1})
    out["points"] = pts
    for key in [(n, 'depth80'), (n, 'depth140')]:
        if key not in cells: continue
        Q = cells[key]
        res = {"contains gstar": all(Q[i][0] <= g[i] <= Q[i][1] for i in range(7))}
        if not res["contains gstar"]:
            res["outside on"] = [i for i in range(7) if not (Q[i][0] <= g[i] <= Q[i][1])]
        used = {}
        kill = []
        for p in pts:
            w = None
            for i in p["lower"]:
                if Q[i][0] < g[i] and (not dyadic(g[i]) or used.get(i, 'lo') == 'lo'):
                    w = ('lo', i); break
            if w is None:
                for k in p["upper"]:
                    if Q[k][1] > g[k] and (not dyadic(g[k]) or used.get(k, 'hi') == 'hi'):
                        w = ('hi', k); break
            if w and dyadic(g[w[1]]): used[w[1]] = w[0]
            kill.append([p["R"], w])
        res["witness per point"] = kill
        res["every point killed, consistently"] = res["contains gstar"] and all(w for _, w in kill)
        res["dyadic witnesses used"] = used
        res["feasible(Q) is None (Q not a leaf)"] = feasible(Q) is None
        out[key[1]] = res
    print(json.dumps(out), flush=True)
