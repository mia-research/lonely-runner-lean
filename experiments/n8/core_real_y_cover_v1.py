# E643 [PROVISIONAL: covering -- claim: a core c of six whole numbers plus ONE extra reading y, any real y in (0, YMAX], is lonely at 1/8 at an instant inside a clear window of c].
# Windows W_j of c within one period (T = 1/g), repeated at W_j + n/g, n = 0..NMAX.  y is served by (j, n, k) when y in [(k+1/8)/(hi_j + n/g), (k+7/8)/(lo_j + n/g)].
# The union of these intervals is built exactly (Fractions) and the complement in (0, YMAX] is reported.  usage: core YMAX NMAX
import sys, math
from fractions import Fraction as F
sys.argv_saved = sys.argv[:]
core = tuple(int(x) for x in sys.argv[1].split(',')); YMAX = F(sys.argv[2]); NMAX = int(sys.argv[3])
from classes_lib_v1 import clear_iv, meet
g = 0
for d in core: g = math.gcd(g, d)
T = F(1, g)
J = clear_iv(F(core[0]), T)
for s in core[1:]: J = meet(J, clear_iv(F(s), T))
J = [(lo, hi) for lo, hi in J if hi >= lo]
iv = []
for lo, hi in J:
    for n in range(NMAX + 1):
        a, b = lo + F(n) * T, hi + F(n) * T
        k = 0
        while F(8 * k + 1, 8) / b <= YMAX:
            iv.append((F(8 * k + 1, 8) / b, F(8 * k + 7, 8) / a)); k += 1
iv.sort()
gaps = []; cur = F(0)
for lo, hi in iv:
    if lo > cur: gaps.append((cur, lo))
    cur = max(cur, hi)
    if cur >= YMAX: break
if cur < YMAX: gaps.append((cur, YMAX))
print('core', core, 'windows', len(J), 'YMAX', YMAX, 'NMAX', NMAX, 'uncovered gaps in (0,YMAX]:', len(gaps), [(str(a), str(b)) for a, b in gaps[:8]])
