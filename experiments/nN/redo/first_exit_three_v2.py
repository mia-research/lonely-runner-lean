"""E239 (2026-10-01): for three whole-number readings and every start t0, two properties, exact:
  P1  some reading's first exit at or after t0 is clear (first_exit_three_v1 tested this one);
  P2  the least clear exit at or after t0 (= the relay's landing g, A.9 and Corollary 6.24) is some reading's first exit
      at or after t0, i.e. the winning flank's index j is 0 (the record read off hole_g_flank_v1.out at f = 3).
P2 implies P1.  Starts: every exit in one period [0, 1) and every midpoint between consecutive exits (the first exits and
the least clear exit after t0 are constant on each open interval).  A start where the block is clear is skipped (g = t0).
Run: (a) every triple <= 80 with spread c/a below 2.2; (b) every triple with 81 <= c <= 160 and spread below 1.62.
Reported: the number of triples failing each property, and the least spread of a failing triple, by height band.
"""
import math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool


def clear_at(S, t):
    for d in S:
        r = (8 * d * t) % 8
        if r < 1 or r > 7:
            return False
    return True


def check(S):
    ex = sorted({F(8 * K + 1, 8 * x) for x in S for K in range(x)})
    ex_all = ex + [e + 1 for e in ex]
    clear_ex = [e for e in ex_all if clear_at(S, e)]
    pts = set(ex)
    for u, v in zip(ex + [ex[0] + 1], ex[1:] + [ex[0] + 1]):
        pts.add((u + v) / 2)
    p1 = p2 = 0; w1 = w2 = None
    for t0 in sorted(pts):
        if clear_at(S, t0):
            continue
        firsts = [F(8 * math.ceil((8 * x * t0 - 1) / 8) + 1, 8 * x) for x in S]
        if not any(clear_at(S, e) for e in firsts):
            p1 += 1; w1 = w1 or t0
        g = next(e for e in clear_ex if e >= t0)
        if g not in firsts:
            p2 += 1; w2 = w2 or t0
    return S, p1, p2, w1, w2


def run(sets):
    return [x for x in (check(S) for S in sets) if x[1] or x[2]]


if __name__ == '__main__':
    out = open('first_exit_three_v2.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    for name, sets in (('(a) triples <= 80, spread below 2.2',
                        [(a, b, c) for c in range(3, 81) for a in range(1, c) if F(c, a) < F(11, 5) for b in range(a + 1, c)]),
                       ('(b) triples 81 <= c <= 160, spread below 1.62',
                        [(a, b, c) for c in range(81, 161) for a in range(1, c) if F(c, a) < F(81, 50) for b in range(a + 1, c)])):
        with Pool(8) as pool:
            bad = [x for part in pool.map(run, [sets[i::256] for i in range(256)]) for x in part]
        w("\n== %s: %d triples ==" % (name, len(sets)))
        for k, lab in ((1, 'P1 (some first exit clear)'), (2, 'P2 (the landing is a first exit)')):
            fl = sorted([x for x in bad if x[k]], key=lambda x: F(x[0][2], x[0][0]))
            w("  failing %s: %d" % (lab, len(fl)))
            if fl:
                bands = {}
                for x in fl:
                    band = (x[0][2] - 1) // 20 * 20 + 1
                    s = F(x[0][2], x[0][0])
                    if band not in bands or s < bands[band][0]:
                        bands[band] = (s, x[0], x[2 + k])
                w("    least spread by band of c: %s" % {b: (round(float(s), 4), S, str(t)) for b, (s, S, t) in sorted(bands.items())})
                w("    the 8 least-spread: %s" % [(x[0], round(float(F(x[0][2], x[0][0])), 4), str(x[2 + k])) for x in fl[:8]])
    out.close()
    print(open('first_exit_three_v2.out').read()[len(__doc__):])
