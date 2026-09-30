"""E214 (2026-10-01): Part B of the Q7 map run with the old landing interval's fate split out.

v1's classes n and m (`q7_map_run_v1.out`) mixed two cases: the move COVERS the interval holding the old landing, or it
OPENS a new interval earlier while the old one survives (the landing is the least clear point, so it moves either way).
Here every move whose landing leaves the old interval is split by: survives = some clear interval after the move meets
the old one.  Recorded per class and fate; for covered cases, where the landing goes (the same pair's mirror junction m;
an interval already clear e; a place the move newly uncovered n).  Same 300 final sets and moves as v1; same checks.
"""
import sys
from collections import Counter
from multiprocessing import Pool
import q7_map_run_v1 as Q
import wide_first_stretch_walk_v1 as W


def study(T):
    T, pair0, npre, rows, checks = Q.study_b(T)
    R0 = Q.landing(T)[0]; I0 = Q.holding(Q.intervals(T), R0)
    out = []
    for cls, i, dl, info in rows:
        if cls in ('s', 'skip', 'x'):
            out.append((cls, None)); continue
        U = Q.moved(T, i, dl)
        survives = any(a <= I0[1] and I0[0] <= b for a, b in Q.intervals(U))
        out.append((cls, 'old interval survives, an earlier one opened' if survives else 'old interval covered'))
    return out, checks


if __name__ == '__main__':
    with Pool(8) as pool:
        finals = [r[1] for r in pool.map(W.walk, [(k, s, 4000) for k, s in enumerate(Q.final_sets())])]
        res = pool.map(study, finals)
    C = Counter(x for r, _ in res for x in r if x[0] not in ('s', 'skip'))
    o = open('q7_map_run_v2.out', 'w'); o.write(__doc__ + "\n")
    o.write("CHECK C1 and M4-1: %d failures\n" % sum(c for _, c in res))
    for k, v in sorted(C.items(), key=lambda kv: (kv[0][1] or '', kv[0][0])):
        o.write("  %s | %s: %d\n" % (k[1], k[0], v))
    o.close(); print(open('q7_map_run_v2.out').read()[len(__doc__):])
