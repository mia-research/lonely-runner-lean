#!/usr/bin/env python3
"""m4_stall_mechanism_v2 -- rule 22 on the STALL boxes (retry3).  At the centre g of the deepest
stalled cell, for each clear-instant window [Rlo, Rhi] in [1,7]: the reading i whose exit edge
(8j+1)/g_i gives Rlo (or 'one' if Rlo = 1), the reading k whose entry edge (8j'+7)/g_k gives Rhi
(or 'seven'), and CLOSES = whether the window would close inside the cell: Rhi - Rlo <=
Rlo*(w_i/g_i) + Rhi*(w_k/g_k) with w the cell's face widths (first-order).  A stall needs every
window to close inside the cell.  Shared pair: one reading pair (i,k) bounding two closing
windows, i.e. g_i/g_k equal to two different edge ratios (8j+1)/(8j'+7) at once."""
import sys, json, collections
sys.path.insert(0, '.')
from fractions import Fraction as F
from m4_fixedpoint_split_v1 import feasible

def bounder(R, g, kind):
    best = None
    for i, x in enumerate(g):
        if x <= 0: continue
        v = R * x
        e = (8 * round((v - 1) / 8) + 1) if kind == 'lo' else (8 * round((v - 7) / 8) + 7)
        d = abs(v - e)
        if best is None or d < best[0]: best = (d, i, e)
    return best

rows = []
for l in open('m4_fixedpoint_split_v1_retry3.jsonl'):
    r = json.loads(l)
    if r.get('status') != 'STALL': continue
    box = [(F(a), F(b)) for a, b in r['box']]
    g = [(a + b) / 2 for a, b in box]; w = [b - a for a, b in box]
    S = feasible([(x, x) for x in g]) or []
    wins = []
    for a, b in S:
        lo = ('one',) if a == 1 else bounder(a, g, 'lo')[1:]
        hi = ('seven',) if b == 7 else bounder(b, g, 'hi')[1:]
        slack = (a * w[lo[0]] / g[lo[0]] if lo[0] != 'one' else 0) + (b * w[hi[0]] / g[hi[0]] if hi[0] != 'seven' else 0)
        wins.append({"R": [float(a), float(b)], "lo": lo, "hi": hi, "closes": bool(b - a <= slack)})
    pairs = collections.Counter((x["lo"][0], x["hi"][0]) for x in wins if x["closes"])
    rows.append({"n": r['n'], "windows": len(wins), "closing": sum(x["closes"] for x in wins),
                 "pairs": {str(k): v for k, v in pairs.items()}, "wins": wins})
for o in rows:
    print(json.dumps(o))
print(json.dumps({"stall_boxes": len(rows), "all_close": sum(o['windows'] == o['closing'] for o in rows),
                  "shared_pair": sum(any(v >= 2 for v in o['pairs'].values()) for o in rows)}))
