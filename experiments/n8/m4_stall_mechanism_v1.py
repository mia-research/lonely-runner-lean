#!/usr/bin/env python3
"""m4_stall_mechanism_v1 -- rule 22 on the STALL boxes of m4_fixedpoint_split_v1_retry3.jsonl.
At the centre g of the deepest stalled box (width < 2^-13 per face), list the clear instants R in
[1,7] (exact) and, for each, the readings sitting within 1e-9 of a gap edge (R*g_i ~ 8j+1 or
8j+7).  An instant is PINCHED when its window is shorter than 1e-6.  Reports, per box: the
pinched instants, the reading pairs pinning each, and whether one pair (a,b) with one ratio
g_a/g_b pins two or more instants (the shared-ratio feature seen at (1,2,4,5,6,7,8))."""
import sys, json, collections
sys.path.insert(0, '.')
from fractions import Fraction as F
from m4_fixedpoint_split_v1 import feasible

def edge_of(v):
    for j in range(40):
        for e in (8*j+1, 8*j+7):
            if abs(v - e) < 1e-9: return e
    return None

out = []
for l in open('m4_fixedpoint_split_v1_retry3.jsonl'):
    r = json.loads(l)
    if r.get('status') != 'STALL': continue
    box = [(F(a), F(b)) for a, b in r['box']]
    g = [(a + b) / 2 for a, b in box]
    S = feasible([(x, x) for x in g]) or []
    pinched = []
    for a, b in S:
        if float(b - a) < 1e-6:
            R = (a + b) / 2
            tight = [(i, edge_of(float(R * x))) for i, x in enumerate(g) if edge_of(float(R * x))]
            pinched.append({"R": float(R), "tight": tight})
    pairs = collections.Counter()
    for p in pinched:
        idx = tuple(sorted(i for i, _ in p["tight"]))
        if len(idx) == 2: pairs[idx] += 1
    shared = [list(k) for k, v in pairs.items() if v >= 2]
    out.append({"n": r['n'], "n_instants": len(S), "pinched": pinched, "shared_pair": shared,
                "g": [round(float(x), 6) for x in g]})
for o in out: print(json.dumps(o))
print(json.dumps({"stall_boxes": len(out), "with_shared_pair": sum(1 for o in out if o['shared_pair']),
                  "all_instants_pinched": sum(1 for o in out if len(o['pinched']) == o['n_instants'])}))
