"""E244/E245 Part A (2026-10-01): the longest blocked stretch of every reduced six-set a1 < ... < a6 <= 32, gcd 1, in laps
of a1.  Design: log E244.

Blocked stretch: a maximal open run of instants with no joint clear point (1/8), between consecutive clear intervals of
the joint clear set over one period [0, 1] (the one through 0 included, wrapping).  Scaling a block by g divides every
instant by g, so G*a1 (laps of the slowest reading) is a property of the reduced set.
Check: every clear interval's left end is an exit (8 a t = 1 mod 8 for some reading) and its right end an entering edge
(= 7 mod 8), and the joint set is clear at both ends (direct evaluation).
Reported: the greatest G*a1 by height band of a6; the 20 largest with their sets and starts s0 (the right end of the
clear interval before the stretch).
"""
import sys, itertools, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set


def clear_at(S, t):
    for d in S:
        r = (8 * d * t) % 8
        if r < 1 or r > 7:
            return False
    return True


def longest(S):
    cs = clear_set(list(S), F(0), F(8))
    iv = [(a / 8, b / 8) for a, b in cs]
    bad = 0
    for a, b in iv:
        if not (clear_at(S, a) and clear_at(S, b)):
            bad += 1
        if not any((8 * d * a) % 8 == 1 for d in S) or not any((8 * d * b) % 8 == 7 for d in S):
            bad += 1
    best = (F(-1), None)
    for (a0, b0), (a1, b1) in zip(iv, iv[1:] + [(iv[0][0] + 1, iv[0][1] + 1)]):
        G = a1 - b0
        if G > best[0]:
            best = (G, b0)
    return S, best[0] * S[0], best[1], bad, len(iv)


def run(sets):
    return [longest(S) for S in sets]


if __name__ == '__main__':
    H = 32
    sets = [S for S in itertools.combinations(range(1, H + 1), 6) if math.gcd(*S) == 1]
    with Pool(8) as pool:
        res = [x for part in pool.map(run, [sets[i::256] for i in range(256)]) for x in part]
    out = open('six_gap_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    w("reduced six-sets <= %d: %d; check failures (ends not clear, or not an exit / entering edge): %d" % (H, len(res), sum(x[3] for x in res)))
    band = {}
    for S, Ga, s0, bad, n in res:
        b = (S[5] - 1) // 4 * 4 + 1
        if b not in band or Ga > band[b][0]:
            band[b] = (Ga, S, s0)
    w("greatest G*a1 (laps of a1) by band of a6: %s" % {b: (round(float(Ga), 4), S, str(s0)) for b, (Ga, S, s0) in sorted(band.items())})
    w("sets by floor(G*a1): %s" % dict(sorted(Counter(int(Ga) for S, Ga, s0, bad, n in res).items())))
    top = sorted(res, key=lambda x: -x[1])[:20]
    w("the 20 largest:")
    for S, Ga, s0, bad, n in top:
        w("   %s  G*a1 %.4f  stretch starts at %s  ratios %s  clear intervals per period %d" % (S, Ga, s0, [round(b / a, 3) for a, b in zip(S, S[1:])], n))
    out.close()
    print(open('six_gap_v1.out').read()[len(__doc__):])
