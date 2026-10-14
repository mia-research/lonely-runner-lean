"""modgap_arc_enum_v1 (2026-10-06): the arc criterion, exhaustively.  For every 7-subset S of [1, TOP] with gcd 1, m = d_min, C = S minus m.  A(S): the cluster C has a lonely instant at 1/7 inside the first clear arc of m,
[1/(7m), 6/(7m)]; exactly: the 1/7-cascade of C started at 1/(7m) has its fixed point (the first lonely instant of C at or after 1/(7m); the cascade from any start at or before the first lonely instant returns it) at most 6/(7m).
[L, E413: lonely_cons_of_arc] A(S) implies S is lonely at 1/7.  Recorded: the number of sets, the number with A(S) false, the false ones by the integer part of rho2 = d_2/d_1 (floor) and the exact least rho2 among them,
the false sets with rho2 >= 9/4 listed (all), and how many false sets are lonely at 1/7 anyway (their lonely instant is later: a later arc of m or none).  Parallel by largest element.  Exact."""
import sys, itertools, math, time, collections
from multiprocessing import Pool
from fractions import Fraction as F
from math import gcd
from functools import reduce
TOP = int(sys.argv[1]) if len(sys.argv) > 1 else 36
H = F(1, 7)
def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
def casc(T, t, cap=400):
    for _ in range(cap):
        B = [x for x in T if cd(x * t) < H]
        if not B: return t
        t = max(F(7 * round(x * t) + 1, 7 * x) for x in B)
    return None
def lonely7(S):
    return casc(S, F(1, 7 * min(S))) is not None
def by_largest(D):
    n = nf = 0; fails = []
    for c in itertools.combinations(range(1, D), 6):
        S = c + (D,)
        if reduce(gcd, S) != 1: continue
        n += 1; m = S[0]; C = S[1:]
        t = casc(C, F(1, 7 * m))
        if t is None or t > F(6, 7 * m): fails.append(S)
    return D, n, fails
if __name__ == '__main__':
    t0 = time.time(); tot = 0; fails = []
    with Pool(4) as pool:
        for D, n, f in pool.imap_unordered(by_largest, range(TOP, 6, -1)):
            tot += n; fails += f
    fails.sort()
    out = open('modgap_arc_enum_v1_top%d.out' % TOP, 'w'); out.write(__doc__ + "\n")
    out.write("[1,%d]: 7-subsets with gcd 1: %d; A(S) false: %d  (elapsed %ds)\n" % (TOP, tot, len(fails), time.time() - t0))
    byrho = collections.Counter(math.floor(F(S[1], S[0])) for S in fails)
    out.write("A(S) false by floor(rho2), rho2 = d2/d1: %s\n" % dict(sorted(byrho.items())))
    rmax = max(F(S[1], S[0]) for S in fails) if fails else None
    out.write("greatest rho2 among the false sets: %s\n" % rmax)
    nl = sum(1 for S in fails if lonely7(S))
    out.write("false sets that are lonely at 1/7 anyway: %d; not lonely at 1/7 (the F7 class): %d\n" % (nl, len(fails) - nl))
    big = [S for S in fails if F(S[1], S[0]) >= F(9, 4)]
    out.write("false sets with rho2 >= 9/4: %d\n" % len(big))
    for S in big[:60]: out.write("  %s  rho2 = %s  lonely at 1/7: %s\n" % (S, F(S[1], S[0]), lonely7(S)))
    out.close(); print(open('modgap_arc_enum_v1_top%d.out' % TOP).read()[len(__doc__):][:5000])
