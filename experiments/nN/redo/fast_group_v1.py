"""E147: the recursion test.  Split each arrangement at its largest consecutive gap: slow group (below) and fast group
G (above).  For landings not at the bound: (a) is the flank in G?  (b) the cascade on G alone, started at the same
instant t0 = 1/(8 d_min), lands at t_G; compare with the full landing t*: equal (the slow group does not delay the fast
group's own point) or later (delayed: by how many further moves, and which slow runner blocks t_G).  Case B to 24 and
the band to 24.  Exact."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade_from(T, t):
    n = 0
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t, n
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way); n += 1
def study(first):
    C = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1]): continue
        band = 'band' if T[-1] <= 9 * T[0] else 'B>9'
        t0 = F(1, 8 * T[0]); ts, _ = cascade_from(T, t0)
        if ts == t0: continue
        gi = max(range(1, 7), key=lambda i: F(T[i], T[i - 1]))
        G = T[gi:]; slow = T[:gi]
        f = next(i for i, d in enumerate(T) if (8 * d * ts) % 8 == 1)
        C[(band, 'flank in the fast group' if f >= gi else 'flank in the slow group')] += 1
        tg, _ = cascade_from(G, t0)
        if tg == ts: C[(band, "full landing = fast group's own landing")] += 1
        else:
            blockers = [d for d in slow if nd(d * tg) < E8]
            C[(band, 'delayed by the slow group (blockers at t_G: %d)' % len(blockers))] += 1
    return C
if __name__ == '__main__':
    C = Counter()
    with Pool(8) as p:
        for c in p.imap_unordered(study, range(1, 19)): C.update(c)
    for k, v in sorted(C.items()): print("  %7d  %s" % (v, k))
