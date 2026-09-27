"""E146: is the landing cluster predictable from the speeds?  Structure read before any landing: the lap-1 clusters
(maximal runs with consecutive ratio below 9/7), numbered 0 (slowest) upward.  Landing: the flank's lap-1 cluster and
whether the flank is that cluster's bottom, and the landing lap k.  Per composition: the distribution of the landing
cluster; the accuracy of the best single choice per composition (an upper bound for any rule using the composition
only); and natural rules: slowest cluster, fastest cluster, the cluster just above the largest gap.  Readings <= 24,
spread in (7, 24] (Case A lands at the bound).  Exact."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter, defaultdict
from multiprocessing import Pool
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
def study(first):
    D = defaultdict(Counter); rules = Counter(); bottom = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1]): continue
        cl = [0]
        for i in range(1, 7): cl.append(cl[-1] + (1 if 7 * T[i] >= 9 * T[i - 1] else 0))
        comp = tuple(Counter(cl)[c] for c in range(cl[-1] + 1))
        t = cascade(T); f = next(i for i, d in enumerate(T) if (8 * d * t) % 8 == 1); k = floor(T[f] * t)
        lc = cl[f]; D[comp][lc] += 1
        bottom['flank is bottom of its lap-1 cluster' if (f == 0 or cl[f - 1] != cl[f]) else 'flank inside its lap-1 cluster'] += 1
        gaps = [F(T[i], T[i - 1]) for i in range(1, 7)]; gi = max(range(6), key=lambda i: gaps[i])  # largest gap between i and i+1
        rules['slowest cluster'] += lc == 0
        rules['fastest cluster'] += lc == cl[-1]
        rules['cluster just above the largest gap'] += lc == cl[gi + 1]
        rules['total'] += 1
    return D, rules, bottom
if __name__ == '__main__':
    D = defaultdict(Counter); R = Counter(); B = Counter()
    with Pool(8) as p:
        for d, r, b in p.imap_unordered(study, range(1, 19)):
            for k, v in d.items(): D[k].update(v)
            R.update(r); B.update(b)
    tot = R['total']; best = sum(max(c.values()) for c in D.values())
    print("sets:", tot, "; compositions:", len(D))
    print("best choice per composition (upper bound for composition-only rules): %d (%.2f%%)" % (best, 100 * best / tot))
    for k in ('slowest cluster', 'fastest cluster', 'cluster just above the largest gap'): print("  rule %-36s %7d (%.2f%%)" % (k, R[k], 100 * R[k] / tot))
    print(" ", dict(B))
    print("compositions with the most spread-out landing:")
    rows = sorted(D.items(), key=lambda kv: -(sum(kv[1].values()) - max(kv[1].values())))[:12]
    for comp, c in rows: print("   ", comp, dict(sorted(c.items())))
