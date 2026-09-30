"""E217 (2026-10-01): the re-aimed run's relocation read on the cascade's own landing (Part B of v1 tracked every lonely
opening in the window, a family broader than the cascade uses).

Same 30 seeded fine shapes and sweeps as `class_instant_run_v1.py` Part B (each reading moved -150..+150 in steps of 5,
readings keeping their names).  At each step the exact cascade's landing, as an opening: setter h and lap K,
t = (8K+1)/(8h).  When the landing's opening changes between consecutive steps (not the same setter and lap):
  - at the OLD landing instant, after the move, which readings are in the way, and on which side of their slot
    (entering side: position mod 8 in (7, 8); leaving side: in [0, 1));
  - whether the NEW landing's setter is a reading that was in the way at the old instant (the isolation pushed to that
    reading's exit), the old setter at another lap, or another reading.
Representation-free (no grid or class chosen).  Check: C1 at every step.
"""
import math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import class_instant_run_v1 as V
from e151_block_v1 import trace


def land_opening(S):
    ts, moves = trace(S)
    h = min(moves[-1][2]) if moves else min(S)
    K = (8 * h * ts - 1) / 8
    return ts, h, K


def sweep(args):
    S0, j = args
    S0 = tuple(sorted(S0)); name0 = S0[j]; prev = None; ev = []; chk = 0
    for dl in range(-150, 151, 5):
        U = list(S0); U[j] = name0 + dl
        if len(set(U)) < 7 or min(U) != S0[0] or U[j] <= S0[0]:
            continue
        S = tuple(sorted(U)); ren = {d: (name0 if d == U[j] else d) for d in S}; inv = {v: k for k, v in ren.items()}
        ts, c1 = V.landing(S); chk += (not c1)
        t, h, K = land_opening(S)
        cur = (ren[h], K, t)
        if prev is not None and (prev[0], prev[1]) != (cur[0], cur[1]):
            told = prev[2]
            way = []
            for d in S:
                p = (8 * d * told) % 8
                if p > 7:
                    way.append((ren[d], 'entering side'))
                elif p < 1:
                    way.append((ren[d], 'leaving side'))
            names = {w[0] for w in way}
            if cur[0] in names:
                rel = 'new setter was in the way at the old landing'
            elif cur[0] == prev[0]:
                rel = 'same setter, another lap'
            else:
                rel = 'another reading'
            ev.append((rel, tuple(sorted(Counter(s for _, s in way).items())), len(way),
                       'moved reading in the way' if name0 in names else 'moved reading clear',
                       'earlier' if cur[2] < told else 'later'))
        prev = cur
    return ev, chk


if __name__ == '__main__':
    shapes = V.fine(218, 30, 2, 20)
    with Pool(8) as pool:
        res = pool.map(sweep, [(S, j) for S in shapes for j in range(1, 7)])
    o = open('class_instant_run_v2.out', 'w'); o.write(__doc__ + "\n")
    o.write("CHECK C1: %d failures\n" % sum(c for _, c in res))
    ev = [e for r, _ in res for e in r]
    o.write("landing jumps (the landing's opening changed between steps): %d\n" % len(ev))
    for k, v in Counter(e[0] for e in ev).most_common():
        o.write("  new landing: %s: %d\n" % (k, v))
    for k, v in Counter((e[4], e[0]) for e in ev).most_common():
        o.write("  %s | %s: %d\n" % (k[0], k[1], v))
    o.write("  readings in the way at the old landing after the move: %s\n" % dict(sorted(Counter(e[2] for e in ev).items())))
    o.write("  their sides: %s\n" % dict(Counter(e[1] for e in ev).most_common(8)))
    o.write("  the moved reading: %s\n" % dict(Counter(e[3] for e in ev)))
    o.close(); print(open('class_instant_run_v2.out').read()[len(__doc__):])
