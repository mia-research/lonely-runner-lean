"""E120: the band remainder's longest cascades, read as the comb sliding.  Exact.
For each remainder set (7 d1 < d7 < 9 d1, no two-block instant) with readings <= N: the cascade's moves; at each move
the window (lap k) that holds each blocker, i.e. which slot-0 window W_k = ((8k-1)/R, (8k+1)/R) the blocker sits in."""
import itertools
from fractions import Fraction as F
from math import floor
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def two_block(T):
    return any(all((e <= 9 * d <= 7 * e) or (e <= d and 9 * d <= 15 * e) for d in T) for e in T)
def cascade(T):
    t = F(1, 8 * T[0]); path = []
    while True:
        R = t * 8 * T[0]
        way = [(d, round(d * t)) for d in T if nd(d * t) < E8]     # blocker and the lap of the window it sits in
        path.append((R, way))
        if not way: return t, path
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d, _ in way)
N = 40; rows = []
for T in itertools.combinations(range(1, N + 1), 7):
    if not (7 * T[0] < T[-1] < 9 * T[0]) or two_block(T): continue
    t, path = cascade(T)
    rows.append((8 * T[0] * t, len(path) - 1, T, path))
rows.sort(key=lambda r: -r[0])
for R, n, T, path in rows[:6]:
    u = [float(F(d, T[0])) for d in T]
    print("set", T, "readings/d1", ["%.3f" % x for x in u], " R* = %s (%.3f), %d moves" % (R, float(R), n))
    for Rm, way in path: print("     R = %-8s %.3f  blockers (reading, window lap): %s" % (Rm, float(Rm), way))
