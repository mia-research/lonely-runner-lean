#!/usr/bin/env python3
"""m4_stall_cut_v2 -- as m4_stall_cut_v1, with the dual test made non-vacuous.

v1's dual test is FORCED: every c = (8a+7)/(8b+1) equals some (8x+1)/(8y+7) (reduce c = A/B;
B odd, so B | 8y+7 is solvable and the quotient's residue mod 8 is then fixed and matches), so
14/14 'shared' says nothing.  v2 asks for a dual that is a WINDOW at the stalled cell: for the cut
g_s/g_r = c, a second pair of edges with reading s on the exit edge 8x+1 and reading r on the
entry edge 8y+7, (8x+1)/(8y+7) = c, at an instant R' = (8y+7)/g_r in [1,7] (g = cell centre).
The cut's own window: reading r on 8a'+1, reading s on 8b'+7 at R = (8a'+1)/g_r in [1,7] with
(8b'+7)/(8a'+1) = c.  SHARED = both windows exist with R != R'.
Control: the same test on every cut of the certificate that does NOT cross the cell."""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import m4_zone_cert_v1 as C

def windows(c, gr):
    """instants R in [1,7] at which reading r sits on an edge and reading s = c*g_r*R on the
    opposite-type edge: kind 'lo' (r on 8a+1, s on 8b+7) or 'hi' (r on 8y+7, s on 8x+1)."""
    out = []
    for e in range(1, 200):
        if e % 8 not in (1, 7): continue
        R = F(e) / gr
        if not (1 <= R <= 7): continue
        f = c * e
        if f.denominator != 1: continue
        f = f.numerator
        if e % 8 == 1 and f % 8 == 7: out.append(("lo", e, f, R))
        if e % 8 == 7 and f % 8 == 1: out.append(("hi", e, f, R))
    return out

def cuts(t, acc):
    if t[0] == "L": return
    _, r, s, p, q, a, b = t
    acc.add((r, s, F(p, q))); cuts(a, acc); cuts(b, acc)

rows = []; ctl = [0, 0]
for l in open('m4_fixedpoint_split_v1_retry3.jsonl'):
    r = json.loads(l)
    if r.get('status') != 'STALL': continue
    n = r['n']; box = [(F(a), F(b)) for a, b in r['box']]
    g = [(a + b) / 2 for a, b in box]
    t, st = C.cert(n, 0)
    acc = set(); cuts(t, acc)
    cross = []
    for (i, k, c) in sorted(acc):
        lo = box[k][0] / box[i][1]; hi = box[k][1] / box[i][0]
        W = windows(c, g[i])
        kinds = {w[0] for w in W}
        shared = kinds == {"lo", "hi"}
        if lo < c < hi:
            cross.append({"r": i, "s": k, "c": str(c), "shared": shared,
                          "windows": [[w[0], w[1], w[2], round(float(w[3]), 5)] for w in W]})
        else:
            ctl[0] += 1; ctl[1] += shared
    rec = {"n": n, "crossing": cross, "shared": sum(1 for x in cross if x["shared"])}
    rows.append(rec); print(json.dumps(rec), flush=True)
print(json.dumps({"stall": len(rows), "with_shared_crossing": sum(1 for r in rows if r["shared"]),
                  "crossing_cuts": sum(len(r["crossing"]) for r in rows),
                  "crossing_shared": sum(r["shared"] for r in rows),
                  "control_noncrossing_cuts": ctl[0], "control_shared": ctl[1],
                  "none": [r["n"] for r in rows if not r["shared"]]}))
