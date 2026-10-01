"""E245/E246 Part A'' (2026-10-01): for every reduced six-set a1 < ... < a6 <= 32 (gcd 1), the largest ratio a blocked
stretch spans from the earliest arc start the hole allows.  Design: log E245.

c's first arc is [s, 7s], s = 1/(8c); the hole needs c <= x1/9, i.e. s >= 9/(8 x1) (in reduced time, 9/(8 a1)).  The first
arc holds no isolation exactly when the block is blocked on all of [s, 7s]: a blocked stretch (s0, s0 + G) with
s0 + G > 7 max(s0, 9/(8 a1)).  Only the first period can do this (a later period spans a ratio at most 2).
Q = max over blocked stretches in the first period of (s0 + G)/max(s0, 9/(8 a1)); the first arc can fail iff Q > 7.
Refutation search for the case "the block's relay from 1/(8c) lands in c's first arc"; a truth check, not a statement.
Check (as six_gap_v1): every clear interval's ends are clear, the left an exit and the right an entering edge.
"""
import sys, itertools, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from six_gap_v1 import clear_at


def q_of(S):
    a1 = S[0]; s_min = F(9, 8 * a1)
    iv = [(a / 8, b / 8) for a, b in clear_set(list(S), F(0), F(8))]
    bad = sum(0 if (clear_at(S, a) and clear_at(S, b)) else 1 for a, b in iv)
    best = (F(0), None, None)
    ends = [F(0)] + [b for a, b in iv]
    starts = [a for a, b in iv] + [iv[0][0] + 1]
    for s0, s1 in zip(ends, starts):
        if s1 <= s_min:
            continue
        q = s1 / max(s0, s_min)
        if q > best[0]:
            best = (q, s0, s1)
    return S, best[0], best[1], best[2], bad


def run(sets):
    return [q_of(S) for S in sets]


if __name__ == '__main__':
    H = 32
    sets = [S for S in itertools.combinations(range(1, H + 1), 6) if math.gcd(*S) == 1]
    with Pool(8) as pool:
        res = [x for part in pool.map(run, [sets[i::256] for i in range(256)]) for x in part]
    out = open('six_gap_v2.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    w("reduced six-sets <= %d: %d; check failures: %d" % (H, len(res), sum(x[4] for x in res)))
    w("sets with Q > 7 (a first arc of c can hold no isolation): %d" % sum(1 for x in res if x[1] > 7))
    band = {}
    for S, q, s0, s1, bad in res:
        b = (S[5] - 1) // 4 * 4 + 1
        if b not in band or q > band[b][0]:
            band[b] = (q, S, s0, s1)
    w("greatest Q by band of a6: %s" % {b: (round(float(q), 4), S, str(s0), str(s1)) for b, (q, S, s0, s1) in sorted(band.items())})
    w("sets by floor(Q): %s" % dict(sorted(Counter(int(q) for S, q, s0, s1, bad in res).items())))
    w("the 20 largest Q:")
    for S, q, s0, s1, bad in sorted(res, key=lambda x: -x[1])[:20]:
        w("   %s  Q %.4f  stretch (%s, %s) = (%.4f, %.4f)  9/(8a1) = %.4f" % (S, q, s0, s1, s0, s1, 9 / (8 * S[0])))
    out.close()
    print(open('six_gap_v2.out').read()[len(__doc__):])
