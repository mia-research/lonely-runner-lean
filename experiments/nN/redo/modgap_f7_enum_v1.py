"""modgap_f7_enum_v1 (2026-10-06): the class F7 of 7-sets with no lonely instant at 1/7, exhaustively on [1, TOP] (TOP = 40) with every d_min, using the forced conditions of the Lean theorems
exists_dvd_of_no_lonely_seven and exists_residue_of_no_lonely_seven as a PREFILTER (a set failing any forced condition is lonely at 1/7 by the contrapositive [L], so it cannot be in F7):
(F1) some reading divisible by each q in 2..7; (F2) some reading = 0, 1, 7 mod 8; (F3) some reading = 0, 3, 5 mod 8.  Survivors are walked exactly (1/7-cascade, cap 300); a capped walk is
confirmed by delta(S) < 1/7 (crossing candidates).  Recorded: the number of survivors of the prefilter, |F7|, the primitive members (gcd 1) with delta, grouped by their six smallest readings (the 'core'),
and which are in the v1 residual (eight_residual).  Parallel by largest element.  Exact."""
import sys, itertools, math, time, collections
from multiprocessing import Pool
from fractions import Fraction as F
TOP_ARG = int(sys.argv[1]) if len(sys.argv) > 1 else 40
sys.argv = [sys.argv[0], '30']
exec(open('../shift_levels_six_eight_v1.py').read().split('t0 = time.time()')[0])
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
def pre(S):
    for q in (5, 7, 4, 3, 2, 6):
        if not any(d % q == 0 for d in S): return False
    if not any(d % 8 in (0, 1, 7) for d in S): return False
    if not any(d % 8 in (0, 3, 5) for d in S): return False
    return True
def by_largest(D):
    surv = 0; f7 = []
    for c in itertools.combinations(range(1, D), 6):
        S = c + (D,)
        if not pre(S): continue
        surv += 1
        if lonely7(S) is None: f7.append(S)
    return D, surv, f7
if __name__ == '__main__':
    TOP = TOP_ARG; t0 = time.time(); surv = 0; f7 = []
    with Pool(4) as pool:
        for D, s, f in pool.imap_unordered(by_largest, range(TOP, 6, -1)):
            surv += s; f7 += f
    f7 = sorted(f7)
    out = open('modgap_f7_enum_v1_top%d.out' % TOP, 'w'); out.write(__doc__ + "\n")
    conf = [S for S in f7 if delta(S) < H]
    prim = [S for S in conf if reduce(gcd, S) == 1]
    out.write("[1,%d]: prefilter survivors %d; capped walks %d; confirmed delta < 1/7: %d; primitive: %d  (elapsed %ds)\n" % (TOP, surv, len(f7), len(conf), len(prim), time.time() - t0))
    cores = collections.defaultdict(list)
    for S in prim: cores[S[:6]].append(S[6])
    for core, xs in sorted(cores.items()):
        out.write("  core %s  + x in %s   (delta of the first: %s)\n" % (core, xs, delta(core + (xs[0],))))
    out.write("primitive F7 sets in the v1 residual (eight_residual): %s\n" % [S for S in prim if eight_residual(S)])
    out.close(); print(open('modgap_f7_enum_v1_top%d.out' % TOP).read()[len(__doc__):])
