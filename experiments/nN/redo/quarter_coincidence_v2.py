"""E426 (2026-10-07), quarter_coincidence_v2: quarter_coincidence_v1's rule (imported unchanged) on the other two
four-odd patterns, (2,5) (f,o,o,o,o) and (1,6) (f,f,o,o,o,o), and the grid-count condition read alongside.  Exact.
Grid-count condition (by hand): at t = m/(4h) a reading a divisible by 4 reads (a/4)*m/h; with g = gcd(a/4, h) and
h' = h/g it is blocked at g*(2*ceil(h'/8) - 1) of the h grid points m/h, at most h/3 when h' >= 3, i.e. when h does
not divide a/2; three such readings all block m = 0, so some m is clear [PROVISIONAL: counting tool; supports: the grid
point of the quarter coincidence].  Recorded: for each set, whether some pair meets the condition ('count'), whether
the exact search finds a clear grid point and a lonely quarter instant ('exact'), and the sets left by both.
Populations: every 7-subset of [1, N] of the pattern (residues mod 8 of the non-multiples: one or two 4s, four odds),
gcd 1, with N = 48 for (2,5) and N = 40 for (1,6).
"""
import sys, itertools, collections
from math import gcd
from functools import reduce
sys.path.insert(0, '.')
from quarter_coincidence_v1 import quarter_pair
def pair_moduli(S):
    odd = [d for d in S if d % 2]; out = []
    for wi, wj in itertools.combinations(odd, 2):
        s = wi - wj if (wi - wj) % 4 == 0 else wi + wj
        out.append(abs(s) // 4)
    return out
def count_condition(S):
    still = [d for d in S if d % 4 == 0]
    return any(h > 0 and all((a // 2) % h for a in still) for h in pair_moduli(S))
if __name__ == '__main__':
    out = open('quarter_coincidence_v2.out', 'w'); out.write(__doc__ + "\n")
    for (m, f, N) in ((2, 1, 48), (1, 2, 40)):
        c = collections.Counter(); left = []; bad = []
        mults = list(range(8, N + 1, 8)); fours = list(range(4, N + 1, 8)); odds = list(range(1, N + 1, 2))
        for M in itertools.combinations(mults, m):
            for Fo in itertools.combinations(fours, f):
                for W in itertools.combinations(odds, 4):
                    S = M + Fo + W
                    if reduce(gcd, S) > 1: continue
                    c['sets'] += 1
                    cc = count_condition(S); r = quarter_pair(S)
                    ex = r not in (None, False) and not isinstance(r[0], str)
                    if isinstance(r, tuple) and isinstance(r[0], str): bad.append((S, r))
                    c[('count', cc, 'exact', ex)] += 1
                    if cc and not ex: bad.append((S, 'count condition holds but exact search found nothing'))
                    if not ex: left.append(S)
        out.write("\nshape (%d,%d), %d of 8 and %d of 4 mod 8, four odd, [1,%d], gcd 1: %s\n" % (m, 7 - m, m, f, N, dict(c)))
        out.write("  contradictions (count condition without an exact instant, or a grid point with no free quarter): %d %s\n" % (len(bad), bad[:3]))
        out.write("  left: %d, first %s\n" % (len(left), left[:12]))
    out.close(); print(open('quarter_coincidence_v2.out').read()[len(__doc__):])
