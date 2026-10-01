"""E239 (2026-10-01): is some reading's first exit after t0 clear, for every three readings and every start t0?

Read off hole_g_flank_v1.out: at f = 3 the winning flank's index is 0 in 1,149 of 1,149 hole relays (the block's relay
lands at some block reading's first exit after t0).  Exhaustive check, exact: whole-number triples a < b < c <= 40; the
first exits after t0 change only when t0 crosses an exit, so t0 is taken in every open interval between consecutive exits
in one period [0, 1), and at every exit itself.  For each (triple, t0): the three first exits at or after t0, and whether
at least one of them has the other two clear (Theorem 6.19's criterion at that opening).  Misses listed, with the
consecutive ratios, to scope the regularity (the hole's blocks have consecutive ratios below 2).
Same check for four readings <= 24 (the f = 4 relays had j = 1 in 11 of 698).
"""
import itertools, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool


def clear_at(S, t):
    for d in S:
        r = (8 * d * t) % 8
        if r < 1 or r > 7:
            return False
    return True


def first_exit(x, t0):
    K = math.ceil((8 * x * t0 - 1) / 8)
    return F(8 * K + 1, 8 * x)


def check(S):
    ex = sorted({F(8 * K + 1, 8 * x) for x in S for K in range(x)} | {F(0), F(1)})
    pts = set(ex[:-1])
    for u, v in zip(ex, ex[1:]):
        pts.add((u + v) / 2)
    miss = []
    for t0 in sorted(pts):
        if clear_at(S, t0):
            continue
        if not any(clear_at(S, first_exit(x, t0)) for x in S):
            miss.append(t0)
    return S, miss


def run(sets):
    return [check(S) for S in sets]


if __name__ == '__main__':
    out = open('first_exit_three_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    for n, top in ((3, 40), (4, 24)):
        sets = list(itertools.combinations(range(1, top + 1), n))
        with Pool(8) as pool:
            res = [x for part in pool.map(run, [sets[i::64] for i in range(64)]) for x in part]
        bad = [(S, m) for S, m in res if m]
        w("\n== %d readings <= %d: %d sets ==" % (n, top, len(sets)))
        w("  sets with some start t0 at which no first exit is clear: %d" % len(bad))
        comp = [(S, m) for S, m in bad if all(b < 2 * a for a, b in zip(S, S[1:]))]
        w("  of these, with every consecutive ratio below 2: %d" % len(comp))
        w("  by max consecutive ratio (floor): %s" % dict(sorted(Counter(int(max(F(b, a) for a, b in zip(S, S[1:]))) for S, m in bad).items())))
        for S, m in (comp[:10] + bad[:10]):
            w("    %s ratios %s  starts %s" % (S, [round(b / a, 3) for a, b in zip(S, S[1:])], [str(t) for t in m[:4]]))
    out.close()
    print(open('first_exit_three_v1.out').read()[len(__doc__):])
