"""E211/E212 (2026-10-01): WideStep8 1 checked as written, before it is registered OWED (F8).

Owner: "yes, design the route first, then build it in lean".  Design: log E211.

  WideStep8 M:  every set S of exactly 7 positive whole numbers, least element m, with some reading above 9m, has
    GridStep8 S m M (BoundClear8 S m, or a grid class through one of its own readings e with mm*m <= M*e, class a unit
    mod 8).  The route: at most six readings (order seven), W <= 7m (the bound), 7m < W <= 9m (band_lonely), 9m < W
    (this statement).  GridStep8 is decided by `least_M` of `cover8_check_v1.py` (written from the Lean definitions).
Populations (seven readings, spread above 9 only):
  every 7-set of readings <= 20; every tenth 7-set of readings <= 24; random 7-sets of readings <= 2,000;
  fine random shapes (least reading 1,000) with spread in (9, 9.5] and in (9.5, 12];
  the edge next to the band: every late band shape (E120-E124; they need M = 2 in the band) with its top reading moved
  to u*m, u in {9.001, 9.01, 9.05, 9.2, 9.5};
  the six-crowd shapes with a slow runner (E153/E154) at crowd scales A putting the top just above 9.
Recorded per population: least M (0 = the bound is clear), and every set with least M >= 2 or none, individually.
"""
import sys, random, itertools
from collections import Counter
from multiprocessing import Pool
from cover8_check_v1 import least_M


def wide(S):
    S = tuple(sorted(S))
    return len(S) == 7 and S[-1] > 9 * S[0]


def run(sets):
    return [(S, least_M(S)) for S in sets]


def report(name, rows, w):
    cnt = Counter(r[1][0] for r in rows)
    w("\n== %s: %d sets ==" % (name, len(rows)))
    w("  least M (0 = the bound is clear): %s" % dict(sorted(cnt.items(), key=lambda kv: (kv[0] is None, kv[0] or 0))))
    bad = [(S, r) for S, r in rows if r[0] is None or r[0] >= 2]
    w("  needing M >= 2, or none up to the cap: %d" % len(bad))
    for S, r in bad[:40]:
        w("    %s  spread %.4f -> %s" % (S, S[-1] / S[0], r))


if __name__ == '__main__':
    sys.path.insert(0, '.')
    from coverB_fine_v1 import late_shapes
    out = open('wide_step_check_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    s20 = [S for S in itertools.combinations(range(1, 21), 7) if wide(S)]
    s24 = [S for S in list(itertools.combinations(range(1, 25), 7))[::10] if wide(S)]
    rng = random.Random(211); rnd = []
    while len(rnd) < 4000:
        S = tuple(sorted(rng.sample(range(1, 2001), 7)))
        if wide(S):
            rnd.append(S)

    def fine(seed, lo, hi, n):
        r = random.Random(seed); outl = []
        while len(outl) < n:
            m = 1000; W = int(r.uniform(lo, hi) * m)
            S = tuple(sorted({m, W} | {r.randrange(m + 1, W) for _ in range(5)}))
            if wide(S):
                outl.append(S)
        return outl
    f1 = fine(1, 9.0005, 9.5, 4000)
    f2 = fine(2, 9.5, 12.0, 3000)
    edge = []
    for T in late_shapes():
        m = T[0]
        for u in (9.001, 9.01, 9.05, 9.2, 9.5):
            S = tuple(sorted(set(T[:-1]) | {int(u * m)}))
            if wide(S):
                edge.append(S)
    sh = (1, 1.3746, 1.7628, 2.2539, 2.5123, 3.23); Dc = 10000; cr = []
    for i in range(200):
        A = 2.79 + 0.002 * i
        S = tuple(sorted({Dc} | {int(round(A * x * Dc)) for x in sh}))
        if wide(S):
            cr.append(S)
    pops = [('every 7-set of readings <= 20, spread above 9', s20),
            ('every tenth 7-set of readings <= 24, spread above 9', s24),
            ('random 7-sets of readings <= 2,000, spread above 9', rnd),
            ('fine shapes, least reading 1,000, spread in (9, 9.5]', f1),
            ('fine shapes, least reading 1,000, spread in (9.5, 12]', f2),
            ('late band shapes with the top reading moved just above 9', edge),
            ('six-crowd shapes with a slow runner, top just above 9', cr)]
    with Pool(8) as pool:
        for name, sets in pops:
            chunks = [sets[i::64] for i in range(64)]
            rows = [r for part in pool.map(run, chunks) for r in part]
            report(name, rows, w)
    out.close()
    print(open('wide_step_check_v1.out').read()[len(__doc__):])
