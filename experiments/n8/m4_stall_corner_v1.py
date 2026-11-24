#!/usr/bin/env python3
"""m4_stall_corner_v1 -- at each STALL cell of retry3, is there a POINT g of the cell (pin g_0 = 1)
with NO clear instant R in [1,7]?  Exact Fractions: feasible() on the point faces (g_i, g_i).
Tested points: the 64 corners of the cell over coordinates 1..6.  A point with feasible() = None
is a reading vector in the box with no clear instant t in [1/8, 7/8], i.e. NoCarve g fails there."""
import sys, json, itertools
sys.path.insert(0, '.')
from fractions import Fraction as F
from m4_fixedpoint_split_v1 import feasible
for l in open('m4_fixedpoint_split_v1_retry3.jsonl'):
    r = json.loads(l)
    if r.get('status') != 'STALL': continue
    box = [(F(a), F(b)) for a, b in r['box']]
    bad = []
    for bits in itertools.product((0, 1), repeat=6):
        g = [box[0][0]] + [box[i + 1][b] for i, b in enumerate(bits)]
        if feasible([(x, x) for x in g]) is None: bad.append(bits)
    print(json.dumps({"n": r['n'], "corners_without_clear_R": len(bad), "first": bad[:3]}))
