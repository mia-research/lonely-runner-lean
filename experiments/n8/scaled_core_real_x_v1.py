# E643: a core c (6 whole numbers) with ONE extra reading y that is any positive rational below the core's threshold.  A scaled core m*c with extra reading x is the core c with y = x/m.
# Question: for core (1,5,6,7,8,13), is c + {y} lonely at 1/8 for every rational y = p/q (q <= QMAX) in (0, 32)?  Exact.  Lonely instant searched at the breakpoints (n+1/8)/d, (n+7/8)/d, n <= NMAX.
import sys, math
from fractions import Fraction as F
core = tuple(int(x) for x in sys.argv[1].split(',')); QMAX = int(sys.argv[2]); YMAX = int(sys.argv[3]); NMAX = int(sys.argv[4])
def dist(x): f = x - math.floor(x); return min(f, 1 - f)
def lonely(S):
    c = sorted({F(8 * n + 1, 8 * d) for d in S for n in range(NMAX)} | {F(8 * n + 7, 8 * d) for d in S for n in range(NMAX)})
    for t in c:
        if t > 0 and all(dist(d * t) >= F(1, 8) for d in S): return t
    return None
bad = []; tested = 0
for q in range(1, QMAX + 1):
    for p in range(1, YMAX * q):
        y = F(p, q)
        if y.denominator != q: continue
        tested += 1
        if lonely(list(map(F, core)) + [y]) is None: bad.append(y)
print('core', core, 'y=p/q, q<=', QMAX, 'y<', YMAX, 'tested', tested, 'no lonely instant found at breakpoints n<', NMAX, ':', len(bad), [str(b) for b in bad[:15]])
