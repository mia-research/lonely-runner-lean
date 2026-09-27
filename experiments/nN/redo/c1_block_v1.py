"""E148: C1 in its simplest form.  Slow group S (below the largest gap, top s_p), fast group G.  From t0 = 1/(8 d_min)
every slow reading has just cleared its first window; S stays clear until 7/(8 s_p) when S's spread <= 7.  For every
landing not at the bound that equals G's own landing: is t_G inside S's first clear block [t0, 7/(8 s_p)]?  Otherwise,
in which of S's later common blocks.  Also the largest gap's size in each case.  Exact."""
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
        S = T[:gi]; G = T[gi:]; gap = F(G[0], S[-1])
        tg, _ = cascade_from(G, t0)
        if tg != ts: C[(band, 'delayed (not G alone)')] += 1; continue
        sspread = F(S[-1], S[0])
        gcls = 'gap >= 15/7' if gap >= F(15, 7) else 'gap in [9/7, 15/7)' if gap >= F(9, 7) else 'gap < 9/7'
        if sspread <= 7 and tg <= F(7, 8 * S[-1]): where = "t_G in S's first clear block"
        else:
            laps = [floor(s * tg) for s in S]
            where = "t_G in a later block of S (S laps %s)" % ('all 0' if max(laps) == 0 else 'mixed')
        C[(band, where, gcls)] += 1
    return C
if __name__ == '__main__':
    C = Counter()
    with Pool(8) as p:
        for c in p.imap_unordered(study, range(1, 19)): C.update(c)
    for k, v in sorted(C.items()): print("  %7d  %s" % (v, k))
