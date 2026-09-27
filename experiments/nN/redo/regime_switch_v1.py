"""E138: regimes and what switches them.  For the 42 band sets whose isolation is at a four-block instant (E137), move one
reading at a time in steps of d_min/12 (readings scaled by 4), up and down, until the cascade's landing changes regime.
Regime of a landing = (flank rank, landing laps).  Record which reading's move switches it, at what step, and the regime
it switches to (AP class instant / two-block / three-block / other).  Exact."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return 8 * T[0] * t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
def regime(T):
    R = cascade(T); s = [F(d, T[0]) for d in T]
    laps = tuple(int(x * R // 8) for x in s)
    return R, laps, max(laps)
SETS = [tuple(map(int, l.split('(')[1].split(')')[0].split(','))) for l in open('proved_union_rem_cascade_v1.out') if l.startswith('   (')]
sw = Counter(); to = Counter(); ex = []
for T0 in SETS:
    T = tuple(4 * d for d in T0); R0, laps0, top0 = regime(T)
    for i in range(1, 7):
        for sgn in (1, -1):
            for step in range(1, 13):
                U = list(T); U[i] += sgn * step
                if U != sorted(U) or len(set(U)) < 7 or not (7 * U[0] < U[-1] <= 9 * U[0]): break
                R, laps, top = regime(tuple(U))
                if laps != laps0:
                    sw[('rank %d' % i, 'up' if sgn > 0 else 'down')] += 1
                    to['top lap %d -> %d' % (top0, top)] += 1
                    if len(ex) < 30: ex.append((T0, i, sgn * step, float(R0), laps0, float(R), laps))
                    break
print("switches by reading moved:"); [print("  %4d  %s" % (v, k)) for k, v in sorted(sw.items())]
print("top lap before -> after:", dict(to))
for e in ex: print("  ", e[0], "move rank %d by %+d/12 d_min" % (e[1], e[2]), "R* %.3f %s -> %.3f %s" % e[3:])
