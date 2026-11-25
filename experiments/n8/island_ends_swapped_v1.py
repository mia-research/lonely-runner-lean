"""E948: the two 'swapped' island ends of island_ends_v3, exactly (2026-11-25).
For each: re-find the end by bisection (as v2), then print, on both sides, the state at the divergent move, the exits of the
readings in the way there, the next state, the readings in the way at the next state, and the landing R*.  Exact Fractions;
floats in the print steer only."""
import sys
from fractions import Fraction as Fr
from math import floor, ceil
exec(open('island_ends_v2.py').read().split("mode = sys.argv[1]")[0])
for idx0, k in ((101498, 5), (101457, 5)):
    row = [r for r in rows if r[0] == idx0][0]
    rs = sorted(Fr(x) for x in rec[idx0][1]); T, _ = cascade(rs, E)
    six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]; hi = rs[k + 1]
    a = rs[k]; g = lambda v: gate(sorted(six + [v]))
    # walk right from the actual position to the first non-crossing point on a fine grid, then bisect
    b = a; st = (hi - a) / 2000
    while g(b): b += st
    for _ in range(120):
        m = (a + b) / 2
        if g(m): a = m
        else: b = m
    print('E340 index', idx0, 'reading', k + 1, 'right end in (%.15f, %.15f)' % (float(a), float(b)))
    for name, v in (('crossing', a), ('other', b)):
        r7 = sorted(six + [v]); Tq, pq, sq, eq = run(r7)
        p = next(u for u in range(len(pq)) if r7.index(pq[u]) + 1 != 0 and u >= 12) if len(pq) > 13 else len(pq) - 1
        for u in range(12, min(len(pq), 16) + 1):
            t = sq[u]; inw = [q + 1 for q in range(7) if blocked(r7[q], t)]
            print('  %s side: move %d state R %.12f set by rank %s | in the way %s | exits %s' % (name, u, float(8 * t), eq[u] + 1 if eq[u] is not None else None, inw,
                  [(q, '%.12f' % float(8 * nxt(r7[q - 1], t))) for q in inw]))
        print('  %s side: R* %.12f, moves %d' % (name, float(8 * Tq), len(pq)))
    # the exact relation at the end: exits of readings 6 and 7 at the state of move 13
    r7 = sorted(six + [a]); Tq, pq, sq, eq = run(r7); t = sq[13]
    m6 = ceil(r7[5] * t - E); m7 = ceil(r7[6] * t - E)
    print('  laps at move 13 state: reading 6 lap', m6, 'reading 7 lap', m7, '| exit(6) - exit(7) at the crossing point (float):', float(8 * (nxt(r7[5], t) - nxt(r7[6], t))))
