#!/usr/bin/env python3
"""m4_stall_cycles_v1 -- the 14 depth-80 STALL cells of retry3 (and the two depth-140 cells): the clear windows at the
cell centre, each end read with the nearest reading edge (m4_wide_blocked_v2.nearest_edges).  A window with lower reading
i at edge 8j+1 and upper reading k at edge 8j'+7 closes on g_k/g_i = (8j'+7)/(8j+1): an edge i -> k with that ratio in
the reading graph.  Every cycle of length 2, 3 or 4 in that graph (edges used in either direction, the ratio inverted
when used backwards): its product P, exact.  P = 1 means the cycle's closing hyperplanes share a ray; P != 1 means they
do not, by the factor P.  Also: the closest-to-1 product per cell, as |P - 1|, and whether the cell's box is one of the
two that reach the cap again."""
import sys, json, itertools
sys.path.insert(0, '.')
from fractions import Fraction as F
from m4_fixedpoint_split_v1 import feasible
from m4_wide_blocked_v2 import nearest_edges
TWO = {(1, 3, 4, 5, 5, 7, 15), (1, 2, 3, 5, 6, 7, 8)}
def cycles(E):
    out = []
    for L in (2, 3, 4):
        for comb in itertools.combinations(range(len(E)), L):
            es = [E[c] for c in comb]
            for orient in itertools.product((1, -1), repeat=L):
                if orient[0] == -1: continue
                seq = [(e[0], e[1], e[2]) if o == 1 else (e[1], e[0], 1 / e[2]) for e, o in zip(es, orient)]
                for perm in itertools.permutations(range(1, L)):
                    path = [seq[0]] + [seq[p] for p in perm]
                    if all(path[t][1] == path[(t + 1) % L][0] for t in range(L)) and len({p[0] for p in path}) == L:
                        P = F(1)
                        for p in path: P *= p[2]
                        out.append((L, [[p[0], p[1], str(p[2])] for p in path], P))
                        break
    return out
def cell_report(n, cell, label):
    g = [(a + b) / 2 for a, b in cell]
    S = feasible([(x, x) for x in g]) or []
    E = [(lo[0], hi[0], F(hi[1], lo[1])) for lo, hi in nearest_edges(g, S) if lo and hi and lo[0] != hi[0]]
    C = cycles(E)
    best = min(C, key=lambda c: abs(c[2] - 1)) if C else None
    return {"n": n, "cell": label, "two": tuple(n) in TWO, "edges": [[i, k, str(q)] for i, k, q in E],
            "cycles": len(C), "P=1 cycles": sum(c[2] == 1 for c in C),
            "closest": None if best is None else {"len": best[0], "path": best[1], "P": str(best[2]), "|P-1|": str(abs(best[2] - 1)), "float": float(abs(best[2] - 1))}}
for l in open('m4_fixedpoint_split_v1_retry3.jsonl'):
    r = json.loads(l)
    if r.get('status') == 'STALL':
        print(json.dumps(cell_report(r['n'], [(F(a), F(b)) for a, b in r['box']], 'depth80')), flush=True)
for l in open('m4_stall_cell_probe_v1.out'):
    r = json.loads(l)
    if 'deeper_cell' in r:
        print(json.dumps(cell_report(r['n'], [(F(a), F(b)) for a, b in r['deeper_cell']], 'depth140')), flush=True)
