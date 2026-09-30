"""E212 (2026-10-01): adversarial walk for a wide set with NO clear point in the slowest reading's first clear stretch.

`BandRoute.gridStep8_one_first_stretch` (proved): GridStep8 S m 1 gives a lonely instant with 1 <= 8mt <= 7.  So a set of
seven readings with spread above 9 and no clear R = 8mt in [1, 7] would refute WideStep8 1.  The late band shapes were
found by exactly this kind of walk inside the band (`coverB_fine_v1.late_shapes`: keep moves that leave [1, 7] unclear).
Here: readings at scale D = 27,720 (least reading D), spread in (9, 12]; one reading moved per step by up to +-600 (the
least reading fixed); a move is kept when the set stays wide and the widest clear interval of R in [1, 7] does not grow
(search instrument only, exact via `band_cert_v1/core.clear_set`).  Starts: the late band shapes with one middle reading
moved above 9 (E212's edge population), and random wide sets.  Every set reaching an empty first stretch is listed with
its least M (cover8_check_v1.least_M) and its first clear R in [1, 40].  Recorded: the least widest-interval reached.
"""
import sys, random
from fractions import Fraction as F
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from cover8_check_v1 import least_M

D = 27720


def widest(T):
    S = clear_set([F(d, D) for d in T], F(1), F(7))
    return max((b - a for a, b in S), default=F(-1))


def walk(args):
    seed, start, steps = args
    rng = random.Random(seed); T = list(start); best = widest(T); hits = []
    for _ in range(steps):
        U = list(T); i = rng.randrange(1, 7); U[i] += rng.randrange(-600, 601); U = sorted(set(U))
        if len(U) < 7 or U[0] != D or not (9 * D < U[-1] <= 12 * D):
            continue
        s = widest(U)
        if s <= best:
            T, best = U, s
            if s < 0:
                hits.append(tuple(U))
    return best, tuple(T), hits[:5]


if __name__ == '__main__':
    from coverB_fine_v1 import late_shapes
    rng = random.Random(212); starts = []
    L = late_shapes()
    for T in rng.sample(L, 150):
        pos = rng.randrange(1, 6); u = rng.choice((9.001, 9.05, 9.5))
        S = sorted((set(T) - {T[pos]}) | {int(u * D)})
        if len(S) == 7:
            starts.append(S)
    while len(starts) < 300:
        W = int(rng.uniform(9.001, 12) * D)
        S = sorted({D, W} | {rng.randrange(D + 1, W) for _ in range(5)})
        if len(S) == 7:
            starts.append(S)
    with Pool(8) as pool:
        res = pool.map(walk, [(k, s, 4000) for k, s in enumerate(starts)])
    out = open('wide_first_stretch_walk_v1.out', 'w'); out.write(__doc__ + "\n")
    ws = sorted(r[0] for r in res)
    out.write("walks: %d x 4000 steps\n" % len(res))
    out.write("least widest clear interval of R in [1,7] reached (-1 = empty): %s\n" % [str(x) for x in ws[:10]])
    out.write("median over walks: %s (float %.5f)\n" % (ws[len(ws) // 2], float(ws[len(ws) // 2])))
    hits = sorted({h for r in res for h in r[2]})
    out.write("sets reaching an empty first stretch: %d\n" % len(hits))
    for h in hits[:30]:
        S = clear_set([F(d, D) for d in h], F(1), F(40))
        out.write("  %s spread %.4f least M %s first clear R %s\n" % (h, h[-1] / D, least_M(h), S[0][0] if S else None))
    lo = sorted(res)[:5]
    for b, T, _ in lo:
        out.write("  nearest: widest %s (%.5f) at %s spread %.4f least M %s\n" % (b, float(b), T, T[-1] / D, least_M(T)))
    out.close()
    print(open('wide_first_stretch_walk_v1.out').read()[len(__doc__):])
