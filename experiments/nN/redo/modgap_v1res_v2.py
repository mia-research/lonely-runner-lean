"""modgap_v1res_v2 (2026-10-06): independent population test.  EVERY 7-subset of [1, TOP] (TOP from the command line: 30, 40, 48, 56) is filtered by the record's v1 residual `eight_residual` (shift_levels_six_eight_v1.py:
EightResidual without the fields added since, in particular without the small-resolution clause), with no construction aimed at 1/7.  Each member of the v1 residual is tested exactly: lonely at 1/7 (the 1/7-cascade of the
full seven readings ends with no reading in the way; walks that hit the cap are re-checked by delta(S) from the crossing candidates) and, for those not lonely at 1/7, the full residual predicate (all 22 fields, incl.
D <= 64 resolution) and delta(S).  Parallel by largest element.  Exact."""
import sys, itertools, math, time, collections
from multiprocessing import Pool
from fractions import Fraction as F
HERE = '../'
TOP_ARG = int(sys.argv[1]) if len(sys.argv) > 1 else 30
sys.argv = [sys.argv[0], '30']
_src = open(HERE + 'shift_levels_six_eight_v1.py').read().split('t0 = time.time()')[0]
exec(_src)
from math import gcd
from functools import reduce
H = F(1, 7)
def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
def lonely7(S, cap=300):
    t = F(1, 7 * min(S))
    for _ in range(cap):
        B = [x for x in S if cd(x * t) < H]
        if not B: return True
        t = max(F(7 * round(x * t) + 1, 7 * x) for x in B)
    return None
def delta(S):
    best = F(0); cands = set()
    for d in S:
        for m in range(d + 1): cands.add(F(2 * m + 1, 2 * d))
    for a, b in itertools.combinations(S, 2):
        for k in range(a + b + 1): cands.add(F(k, a + b))
        if a != b:
            for k in range(abs(b - a) + 1): cands.add(F(k, abs(b - a)))
    for t in cands:
        if 0 < t <= F(1, 2):
            v = min(cd(x * t) for x in S)
            if v > best: best = v
    return best
def by_largest(D):
    n = 0; lon = 0; bad = []
    for c in itertools.combinations(range(1, D), 6):
        S = c + (D,)
        if reduce(gcd, S) != 1: continue
        if eight_residual(S):
            n += 1
            r = lonely7(S)
            if r: lon += 1
            else: bad.append(S)
    return D, n, lon, bad
if __name__ == '__main__':
    TOP = TOP_ARG
    t0 = time.time(); tot = lonT = 0; bad = []
    with Pool(4) as pool:
        for D, n, lon, b in pool.imap_unordered(by_largest, range(TOP, 6, -1)):
            tot += n; lonT += lon; bad += b
    out = open('modgap_v1res_v2_top%d.out' % TOP, 'w'); out.write(__doc__ + "\n")
    out.write("7-subsets of [1,%d] with gcd 1 in the v1 residual (eight_residual): %d; lonely at 1/7: %d; not lonely at 1/7: %d  (elapsed %ds)\n" % (TOP, tot, lonT, len(bad), time.time() - t0))
    for S in sorted(bad):
        out.write("  not 1/7-lonely: %s  delta = %s  in the full residual predicate (all 22 fields): %s\n" % (S, delta(S), __import__('members_reach_check_v1').full_residual(S)))
    out.close(); print(open('modgap_v1res_v2_top%d.out' % TOP).read()[len(__doc__):])
