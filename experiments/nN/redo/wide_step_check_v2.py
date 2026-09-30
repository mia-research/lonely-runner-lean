"""E212 (2026-10-01): WideStep8 1 at the edge next to the band, with the bound blocked (v1's edge population replaced).

v1 (`wide_step_check_v1.out`) moved each late band shape's TOP reading to u*m, u in (9, 9.5].  That population is
bound-clear by construction (F5): the other six readings are in [m, 7m] and u*m is in [9m, 15m], so every reading lies in
[1/8, 7/8] at the bound; its 27,000 zeros test nothing.  Here the edge keeps what made the late shapes late:
  (a) every late band shape (top reading in (7m, 7.44m], blocked at the bound) with ONE MIDDLE reading (positions 1-5)
      replaced by u*m, u in {9.001, 9.05, 9.5}: spread just above 9 with the old top still blocked;
  (b) fine shapes (least reading 1,000), spread in (9, 9.2], with at least one reading in (7m, 9m) (blocked at the bound).
Decided by `least_M` of `cover8_check_v1.py`.  Recorded: least M, whether the bound is blocked (it must be, in (a) and
(b)), and every set needing M >= 2 or none, individually.
"""
import sys, random
from collections import Counter
from multiprocessing import Pool
from cover8_check_v1 import least_M, bound_clear
from wide_step_check_v1 import wide


def run(sets):
    return [(S, least_M(S), bound_clear(S, S[0])) for S in sets]


def report(name, rows, w):
    w("\n== %s: %d sets ==" % (name, len(rows)))
    w("  CHECK the bound is blocked in every set (by construction): %d bound-clear" % sum(1 for r in rows if r[2]))
    w("  least M: %s" % dict(sorted(Counter(r[1][0] for r in rows).items(), key=lambda kv: (kv[0] is None, kv[0] or 0))))
    w("  the grid used at least M = 1 (e, mm, c), most common: %s" %
      Counter((r[1][1][0] == r[0][0], r[1][1][1], r[1][1][2]) for r in rows if r[1][1]).most_common(6))
    bad = [(S, r) for S, r, b in rows if r[0] is None or r[0] >= 2]
    w("  needing M >= 2, or none up to the cap: %d" % len(bad))
    for S, r in bad[:40]:
        w("    %s  spread %.4f -> %s" % (S, S[-1] / S[0], r))


if __name__ == '__main__':
    sys.path.insert(0, '.')
    from coverB_fine_v1 import late_shapes
    out = open('wide_step_check_v2.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    edge = []
    for T in late_shapes():
        m = T[0]
        for pos in range(1, 6):
            for u in (9.001, 9.05, 9.5):
                S = tuple(sorted((set(T) - {T[pos]}) | {int(u * m)}))
                if wide(S):
                    edge.append(S)
    edge = sorted(set(edge))
    r = random.Random(3); fb = []
    while len(fb) < 6000:
        m = 1000; W = int(r.uniform(9.0005, 9.2) * m)
        S = tuple(sorted({m, W} | {r.randrange(m + 1, W) for _ in range(5)}))
        if wide(S) and any(7 * m < d < 9 * m for d in S):
            fb.append(S)
    with Pool(8) as pool:
        for name, sets in (('late band shapes with one middle reading moved just above 9 (old top still blocked)', edge),
                           ('fine shapes, spread in (9, 9.2], a reading in (7m, 9m)', fb)):
            chunks = [sets[i::64] for i in range(64)]
            report(name, [x for part in pool.map(run, chunks) for x in part], w)
    out.close()
    print(open('wide_step_check_v2.out').read()[len(__doc__):])
