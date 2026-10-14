"""E400 (2026-10-05), mixed_threshold_v1: the mixed problem M(C; U) left by an f-walker's silence.

Derived (by hand): a non-multiple f = 4u (u odd) blocks a whole parity class of the eight shifts when
||u*tau|| < 1/4 and blocks no shift when ||u*tau|| >= 1/4 (its offset f*tau mod 8 lies in [1,3] or [5,7]).
Every other non-multiple blocks at most two shifts.  So a residual pattern whose non-multiples other than the
f-walkers number at most three is settled at any tau that clears the cofactors C (||c*tau|| >= 1/8) and silences
every f-walker (||u*tau|| >= 1/4 for u = f/4)  [PROVISIONAL: counting tool; supports: a free shift at such tau].
Patterns concerned: (3,4) (f,o,o,t): C of size 3, U of size 1; (2,5) (f,f,o,o,t): 2 and 2; (1,6) (f,f,f,o,o,t): 1 and 3.

M(C; U): is there tau with ||c*tau|| >= 1/8 for c in C and ||u*tau|| >= 1/4 for u in U?  Exact (Fractions):
the clear set is a finite union of closed intervals of period 1; if non-empty, one of its points is a left
endpoint (j + 1/8)/c or (j + 1/4)/u with 0 <= j < c (resp. u), so testing those candidates decides it.
Recorded: for each size pair, every C (distinct, from [1, N]) and every U (distinct odd, from [1, N]) - all
pairs, not a sample - the number with no solution, and the first ones listed.
"""
import itertools, math, sys
from fractions import Fraction as F

def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)

def solvable(C, U):
    cands = [F(8 * j + 1, 8 * c) for c in C for j in range(c)] + [F(4 * j + 1, 4 * u) for u in U for j in range(u)]
    for t in cands:
        if all(cd(c * t) >= F(1, 8) for c in C) and all(cd(u * t) >= F(1, 4) for u in U):
            return t
    return None

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    out = open('mixed_threshold_v1.out', 'w'); out.write(__doc__ + "\n")
    odds = [u for u in range(1, N + 1) if u % 2]
    for (nc, nu) in ((3, 1), (2, 2), (1, 3)):
        tot = 0; bad = []
        for C in itertools.combinations(range(1, N + 1), nc):
            for U in itertools.combinations(odds, nu):
                tot += 1
                if solvable(C, U) is None: bad.append((C, U))
        out.write("|C| = %d, |U| = %d, values <= %d: pairs %d, with no solution %d\n" % (nc, nu, N, tot, len(bad)))
        for b in bad[:25]: out.write("   no solution: C = %s, U = %s\n" % b)
    out.close(); print(open('mixed_threshold_v1.out').read()[len(__doc__):])
