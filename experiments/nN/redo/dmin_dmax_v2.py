"""E146 v2: as v1 but clusters cut at the landing lap's rho_k (the confirmed type definition).  Middle landings then
described by: the flank's cluster index from the top (1 = fastest), the clusters above it (their sizes), and whether the
flank lies above the largest consecutive gap.  Exact."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
from dmin_dmax_v1 import cascade
def study(first):
    C = Counter(); M = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1]): continue
        band = 'band' if T[-1] <= 9 * T[0] else 'B>9'
        t = cascade(T); f = next(i for i, d in enumerate(T) if (8 * d * t) % 8 == 1); k = floor(T[f] * t)
        if k == 0: C[(band, 'd_min: at the bound')] += 1; continue
        cl = [0]
        for i in range(1, 7): cl.append(cl[-1] + (1 if (8 * k - 1) * T[i] >= (8 * k + 1) * T[i - 1] else 0))
        if cl[f] == cl[-1]: C[(band, 'd_max: bottom of the fastest cluster at rho_k')] += 1; continue
        C[(band, 'middle')] += 1
        above = tuple(Counter(cl[f + 1:]).values())
        gi = max(range(1, 7), key=lambda i: F(T[i], T[i - 1]))
        M[(band, 'flank cluster %d from the top' % (cl[-1] - cl[f] + 1), 'clusters above: %s' % (above,), 'flank above the largest gap' if f >= gi else 'flank below the largest gap')] += 1
    return C, M
if __name__ == '__main__':
    C = Counter(); M = Counter()
    with Pool(8) as p:
        for c, m in p.imap_unordered(study, range(1, 19)): C.update(c); M.update(m)
    for k, v in sorted(C.items()): print("  %7d  %s" % (v, k))
    print("middle landings, commonest descriptions:")
    for k, v in M.most_common(20): print("  %7d  %s" % (v, k))
