"""modgap_arc_threshold_v1 (2026-10-06): does the arc criterion A(S) (the cluster C = S minus d_min has a lonely instant at 1/7 in [1/(7m), 6/(7m)], exactly: the cascade of C started at 1/(7m) lands at most 6/(7m)) hold whenever d_2 >= 5 d_1?
Exhaustive search over the sets with d_1 = m (m = 5..12) and d_2 = 5m - 1 (just below the threshold) and d_2 in {5m, 5m + 1} (at and above), the other five readings any distinct integers in (d_2, 8m]
(d_7 <= 8m: the failures seen on [1,44] have d_7/d_1 <= 11, and 8m covers the layer just above R1 at 1/7).  Recorded per (m, d_2): the number of sets with gcd 1, the number with A(S) false, and the
sets with A(S) false at d_2 >= 5m listed in full.  Exact.  Parallel by m."""
import sys, itertools, math, collections, time
from multiprocessing import Pool
from fractions import Fraction as F
from math import gcd
from functools import reduce
H = F(1, 7)
def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
def casc(T, t, cap=400):
    for _ in range(cap):
        B = [x for x in T if cd(x * t) < H]
        if not B: return t
        t = max(F(7 * round(x * t) + 1, 7 * x) for x in B)
    return None
def run(args):
    m, d2 = args
    n = nf = 0; fails = []
    for rest in itertools.combinations(range(d2 + 1, 8 * m + 1), 5):
        S = (m, d2) + rest
        if reduce(gcd, S) != 1: continue
        n += 1
        t = casc(S[1:], F(1, 7 * m))
        if t is None or t > F(6, 7 * m): nf += 1; fails.append(S)
    return m, d2, n, nf, fails
if __name__ == '__main__':
    t0 = time.time(); jobs = [(m, d2) for m in range(5, 13) for d2 in (5 * m - 1, 5 * m, 5 * m + 1)]
    out = open('modgap_arc_threshold_v1.out', 'w'); out.write(__doc__ + "\n")
    res = []
    with Pool(4) as pool:
        for r in pool.imap_unordered(run, jobs): res.append(r)
    res.sort()
    for m, d2, n, nf, fails in res:
        out.write("m = %2d, d_2 = %3d (rho2 = %s; d_2 %s 5m): sets %9d, A false %6d%s\n" % (m, d2, F(d2, m), '>=' if d2 >= 5 * m else '<', n, nf, "  <-- failures at d_2 >= 5m" if (nf and d2 >= 5 * m) else ""))
        if d2 >= 5 * m:
            for S in fails[:10]: out.write("      A false: %s\n" % (S,))
    out.write("elapsed %ds\n" % (time.time() - t0))
    out.close(); print(open('modgap_arc_threshold_v1.out').read()[len(__doc__):])
