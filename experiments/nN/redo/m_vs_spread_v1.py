"""E164: is the needed grid fineness m independent of the spread?  Random wide sets (spread 25..2000, log-uniform) and
Case B to 24: least m (grid through a reading at scale s_j/m, class c in {1,3,5,7}, exact Helly) by spread band; and the
least m (up to 64) for the 15 sets that needed m > 8.  Protections: progress file, caffeinate by the caller."""
import itertools, random, ast, sys
from fractions import Fraction as F
from math import exp, log
from collections import Counter, defaultdict
from multiprocessing import Pool
from casec_gridclass_v1 import least_m
PROG = 'm_vs_spread_v1.progress'
def band(S):
    for lo, hi in ((7, 9), (9, 24), (24, 100), (100, 400), (400, 2001)):
        if lo < S <= hi: return '%d-%d' % (lo, hi)
    return 'other'
def p2(seed):
    rng = random.Random(1000 + seed); C = Counter()
    for _ in range(1500):
        dmin = rng.randrange(1, 60); S = rng.uniform(7.01, 2000)
        xs = sorted({max(dmin + 1, int(round(dmin * exp(rng.uniform(0, log(S)))))) for _ in range(5)} | {dmin, int(dmin * S)})
        if len(xs) != 7 or xs[-1] <= 7 * xs[0]: continue
        C[(band(xs[-1] / xs[0]), least_m(tuple(xs), 12))] += 1
    open(PROG, 'a').write("seed %d done\n" % seed)
    return C
if __name__ == '__main__':
    open(PROG, 'w').write("start\n")
    with Pool(8) as p:
        C = Counter()
        for c in p.imap_unordered(p2, range(16)): C.update(c)
    by = defaultdict(Counter)
    for (b, m), v in C.items(): by[b][m] += v
    for b in sorted(by): print("spread %-9s least m: %s" % (b, sorted(by[b].items(), key=lambda kv: (kv[0] is None, kv[0] or 0))))
    line = [l for l in open('casec_gridclass_v1.out') if l.startswith('P2')][0]
    U = ast.literal_eval(line.split('uncovered (m<=8): ')[1].split(' ', 1)[1])
    with Pool(8) as p: res = p.starmap(least_m, [(T, 64) for T in U])
    print("the 15 captures: least m up to 64:", [(round(T[-1] / T[0]), r) for T, r in zip(U, res)])
    open(PROG, 'a').write("ALLDONE\n")
