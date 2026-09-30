"""E210 (2026-09-30): Cover8 M checked as written: an independent implementation from the Lean definition.

Owner: "yes commit the band cover, then check Cover8 M".  Map: E209 point 4 (F8: a `def ... : Prop` is type-checked,
never proved).  Written from `LonelyRunner/LRC/Spec/RegimeSkeletonN.lean` (BoundClear8, GridClass8, GridStep8, Cover8),
not from E165's `cover8_step_v1.py`.

  Cover8 M:  every finite set S of at most 7 positive whole numbers, least element m, has GridStep8 S m M:
    BoundClear8 S m  (every d: circDist(d/(8m)) >= 1/8), or
    some e in S, mm >= 1 with mm*m <= M*e, c in {1,3,5,7}, and GridClass8 S e mm c: a lap k(d) for every d, from a grid
    point n >= 1 with |n*e - mm*d| < e, k(d) = floor(c n / 8), or k(d) + 1 = c n / 8 when c n = 0 mod 8; the laps
    pairwise compatible, (8 k(d) + 1) d' <= (8 k(d') + 7) d.
  Pairwise compatibility is decided exactly as 1-D Helly (`lonely_eight_of_pairwise_laps`): some t lies in every chosen
  block [(8k+1)/(8d), (8k+7)/(8d)]; the candidates for t are the blocks' left ends.  GridStep8 is monotone in M, so each
  set's LEAST M is recorded (the least ceil(mm*m/e) over the classes that work).
Populations: every subset of 1..16 of 1 to 7 readings (sets with fewer than 7 readings are inside Cover8 and were not in
E165); every 7-set of readings <= 20; every tenth 7-set of readings <= 24; the late fine band shapes; the band's
extremal shape (E121) and the six-crowd shapes with a slow runner (E153/E154), integerised; random wide sets of 2 to 7
readings up to 2,000.  Pass condition: none, this is a check of a statement's truth on these populations; every set
needing M >= 3, or none up to the cap, is listed.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool

MCAP = 8


def bound_clear(S, m):
    for d in S:
        x = F(d, 8 * m); f = x - math.floor(x)
        if f < F(1, 8) or f > F(7, 8):
            return False
    return True


def lap_options(d, e, mm, c):
    out = set()
    for n in (mm * d // e, mm * d // e + 1):
        if n >= 1 and abs(n * e - mm * d) < e:
            q, r = divmod(c * n, 8)
            out.add(q)
            if r == 0 and q >= 1:
                out.add(q - 1)
    return out


def grid_class(S, e, mm, c):
    opts = []
    for d in S:
        o = lap_options(d, e, mm, c)
        if not o:
            return False
        opts.append([(F(8 * k + 1, 8 * d), F(8 * k + 7, 8 * d)) for k in o])
    cands = sorted({a for ivs in opts for a, b in ivs})
    for t in cands:
        if all(any(a <= t <= b for a, b in ivs) for ivs in opts):
            return True
    return False


def least_M(S):
    S = sorted(S); m = S[0]
    if bound_clear(S, m):
        return 0, None                                  # M irrelevant: the bound
    best = None
    for e in S:
        for mm in range(1, MCAP * e // m + 1):
            need = -(-mm * m // e)                       # ceil(mm m / e)
            if best is not None and need >= best[0]:
                break
            for c in (1, 3, 5, 7):
                if grid_class(S, e, mm, c):
                    best = (need, (e, mm, c)); break
    return (best[0], best[1]) if best else (None, None)


def run(sets):
    return [(S, least_M(S)) for S in sets]


def report(name, rows, w):
    cnt = Counter(r[1][0] for r in rows)
    w("\n== %s: %d sets ==" % (name, len(rows)))
    w("  least M (0 = the bound is clear): %s" % dict(sorted(cnt.items(), key=lambda kv: (kv[0] is None, kv[0] or 0))))
    bad = [(S, r) for S, r in rows if r[0] is None or r[0] >= 3]
    w("  needing M >= 3 or none up to %d: %d" % (MCAP, len(bad)))
    for S, r in bad[:25]:
        w("    %s -> %s" % (S, r))


if __name__ == '__main__':
    sys.path.insert(0, '.')
    from coverB_fine_v1 import late_shapes
    out = open('cover8_check_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    small = [S for k in range(1, 8) for S in itertools.combinations(range(1, 17), k)]
    s20 = list(itertools.combinations(range(1, 21), 7))
    s24 = list(itertools.combinations(range(1, 25), 7))[::10]
    D = 27720
    ext = [tuple(sorted({int(round(x * D)) for x in (1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378)}))]
    crowds = [(1, 1.3746, 1.7628, 2.2539, 2.5123, 3.23)]
    Dc = 10000; cr = []
    for sh in crowds:
        for A in [1.7 + 0.1 * i for i in range(104)]:
            S = tuple(sorted({Dc} | {int(round(A * x * Dc)) for x in sh}))
            if len(S) == 7:
                cr.append(S)
    rng = random.Random(7); wide = []
    while len(wide) < 3000:
        k = rng.randrange(2, 8)
        wide.append(tuple(sorted(rng.sample(range(1, 2001), k))))
    pops = [('every subset of 1..16 with 1 to 7 readings', small), ('every 7-set of readings <= 20', s20),
            ('every tenth 7-set of readings <= 24', s24), ('late fine band shapes', late_shapes()),
            ("the band's extremal shape (E121)", ext), ('six-crowd shapes with a slow runner (E153/E154)', cr),
            ('random sets of 2 to 7 readings up to 2,000', wide)]
    with Pool(8) as pool:
        for name, sets in pops:
            chunks = [sets[i::64] for i in range(64)]
            rows = [r for part in pool.map(run, chunks) for r in part]
            report(name, rows, w)
    out.close()
    print(open('cover8_check_v1.out').read()[len(__doc__):])
