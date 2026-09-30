"""E214 (2026-10-01): the Q7 map run's covering moves that did not go to the pair's mirror, listed; and the grid-pair-law
reading of the tight set checked.

(1) Part B (v2): of 261 moves that cover the interval holding the old landing, 106 go to an interval already clear (e),
140 to the same pair's mirror junction (m), 15 to a place newly uncovered (n).  e is forced whenever the set had another
clear interval (M4-1: the landing is the least clear point); checked here.  The 15 n are listed individually.
(2) The tight set's two points against `GridPairLawN.grid_pair_law`: the pair's readings at R1, R2 are c*n on the grid
through 117495 with divisor 5 (grid points n_a = 5, n_b = 11), classes c = 3 and c' = 5 = 8 - 3 (mirror); checked exactly,
with every other reading's grid position and deviation (grid step 117495/5) listed.
"""
import sys
from fractions import Fraction as F
from multiprocessing import Pool
import q7_map_run_v1 as Q
import wide_first_stretch_walk_v1 as W


def study(T):
    T = tuple(sorted(T))
    R0 = Q.landing(T)[0]; pre = Q.intervals(T); I0 = Q.holding(pre, R0); pair0 = Q.bounding(T, I0)
    e_forced = []; ns = []
    for i in range(1, 7):
        for sg in (1, -1):
            for d in Q.DELTAS:
                U = Q.moved(T, i, sg * d)
                if U is None:
                    continue
                R = Q.landing(U)[0]
                if R > 7:
                    continue
                post = Q.intervals(U)
                if any(a <= I0[1] and I0[0] <= b for a, b in post):
                    continue                                         # old interval survives
                I1 = Q.holding(post, R)
                if any(I1[0] <= b and a <= I1[1] for a, b in pre):
                    e_forced.append(len(pre) >= 2); continue
                new = T[i] + sg * d
                orig = lambda v: T[i] if v == new else v
                l1 = {orig(v) for v in Q.bounding(U, I1)[0]}; r1 = {orig(v) for v in Q.bounding(U, I1)[1]}
                if l1 & set(pair0[1]) and r1 & set(pair0[0]):
                    continue                                         # m
                ns.append((T, i, sg * d, pair0, tuple(sorted(l1)), tuple(sorted(r1)), float(R0), float(R), len(pre)))
    return e_forced, ns


if __name__ == '__main__':
    o = open('q7_map_run_v3.out', 'w'); o.write(__doc__ + "\n")
    with Pool(8) as pool:
        finals = [r[1] for r in pool.map(W.walk, [(k, s, 4000) for k, s in enumerate(Q.final_sets())])]
        res = pool.map(study, finals)
    ef = [x for r in res for x in r[0]]
    o.write("(1) e moves: %d; the set had another clear interval in %d (forced)\n" % (len(ef), sum(ef)))
    ns = [x for r in res for x in r[1]]
    o.write("    n moves (covered, landing at a newly uncovered place, not the mirror): %d\n" % len(ns))
    for T, i, dl, p0, l1, r1, R0, R, npre in ns:
        o.write("      %s rank %d %+d | old pair exit %s enter %s at R %.4f | new exit %s enter %s at R %.4f | %d intervals before\n"
                % (T, i, dl, p0[0], p0[1], R0, l1, r1, R, npre))
    T = Q.TIGHT; e = T[2]; g = F(e, 5)
    ivs = Q.intervals(T)
    o.write("(2) tight set %s; grid step %s (117495/5)\n" % (T, g))
    for R, c in ((ivs[0][0], 3), (ivs[1][0], 5)):
        o.write("    R %s: class %d\n" % (R, c))
        for d in T:
            x = F(d) / g; n = round(x); P = F(d, T[0]) * R
            o.write("      reading %d: grid point %d, deviation %.4f; position %s = %s mod 8; c*n = %d = %d mod 8\n"
                    % (d, n, float(x - n), P, P % 8, c * n, (c * n) % 8))
    o.close(); print(open('q7_map_run_v3.out').read()[len(__doc__):])
