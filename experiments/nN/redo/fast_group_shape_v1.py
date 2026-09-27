"""E149: the fast group G at its landing inside the slow group's first block.  For each d_max landing (G's own landing,
in S's first block): |G|, G's spread, the landing lap k (flank's), whether all of G is on one lap (G lands as one crowd:
a common block of G) or split across laps (then: the split point is G's own largest gap?).  Exact."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
from fast_group_v1 import cascade_from
def study(first):
    C = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1]): continue
        band = 'band' if T[-1] <= 9 * T[0] else 'B>9'
        t0 = F(1, 8 * T[0]); ts, _ = cascade_from(T, t0)
        if ts == t0: continue
        gi = max(range(1, 7), key=lambda i: F(T[i], T[i - 1]))
        S = T[:gi]; G = T[gi:]
        tg, _ = cascade_from(G, t0)
        if tg != ts or not (tg <= F(7, 8 * S[-1])): continue
        laps = [floor(g * tg) for g in G]
        if len(set(laps)) == 1: how = 'G on one lap (a common block of G)'
        else:
            # split: where do the laps change, and is it at G's largest internal gap?
            ch = [i for i in range(1, len(G)) if laps[i] != laps[i - 1]]
            if len(G) > 1:
                gg = max(range(1, len(G)), key=lambda i: F(G[i], G[i - 1]))
                how = 'G split over %d laps; %s' % (len(set(laps)), 'first split at G\'s largest gap' if ch[0] == gg else 'first split elsewhere')
        C[(band, '|G| = %d' % len(G), how)] += 1
    return C
if __name__ == '__main__':
    C = Counter()
    with Pool(8) as p:
        for c in p.imap_unordered(study, range(1, 19)): C.update(c)
    for k, v in sorted(C.items()): print("  %7d  %s" % (v, k))
