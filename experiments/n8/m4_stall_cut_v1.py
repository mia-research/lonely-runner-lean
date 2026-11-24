#!/usr/bin/env python3
"""m4_stall_cut_v1 -- rule 22 (ii)/(iii) on the 14 STALL cells, from the zone certificates.

For each STALL box: its zone certificate (m4_zone_cert_v1.cert, w = 0); every cut of the tree is
a ratio hyperplane g_s / g_r = c with c = (8 m_s + 7)/(8 m_r + 1) (a face of a zone C_m).  List
the cuts that cross the stalled cell of retry3 (c strictly inside the cell's ratio range
[lo_s/hi_r, hi_s/lo_r]).  A crossing cut is SHARED-RATIO when c also equals (8x+1)/(8y+7) for
some x, y >= 0: the same hyperplane is then a face of a second zone, on the other side (one
window closes where the other opens).  Exact Fractions."""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import m4_zone_cert_v1 as C

def dual(c):
    # c = (8x+1)/(8y+7): search y with (8y+7)*c = 8x+1 an integer = 1 mod 8
    for y in range(0, 200):
        v = (8 * y + 7) * c
        if v.denominator == 1 and v.numerator % 8 == 1: return (int((v.numerator - 1) // 8), y)
    return None

def cuts(t, acc):
    if t[0] == "L": return
    _, r, s, p, q, a, b = t
    acc.add((r, s, F(p, q))); cuts(a, acc); cuts(b, acc)

rows = []
for l in open('m4_fixedpoint_split_v1_retry3.jsonl'):
    r = json.loads(l)
    if r.get('status') != 'STALL': continue
    n = r['n']; box = [(F(a), F(b)) for a, b in r['box']]
    t, st = C.cert(n, 0)
    acc = set(); cuts(t, acc)
    cross = []
    for (i, k, c) in sorted(acc):
        lo = box[k][0] / box[i][1]; hi = box[k][1] / box[i][0]
        if lo < c < hi:
            d = dual(c)
            cross.append({"r": i, "s": k, "c": str(c), "dual": None if d is None else f"(8*{d[0]}+1)/(8*{d[1]}+7)"})
    rec = {"n": n, "cuts": len(acc), "crossing": cross, "shared": sum(1 for x in cross if x["dual"])}
    rows.append(rec); print(json.dumps(rec), flush=True)
print(json.dumps({"stall": len(rows), "with_crossing": sum(1 for r in rows if r["crossing"]),
                  "with_shared_crossing": sum(1 for r in rows if r["shared"]),
                  "none": [r["n"] for r in rows if not r["shared"]]}))
