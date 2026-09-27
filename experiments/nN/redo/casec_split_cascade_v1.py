"""E155: Case C arrangements whose slow group (below the largest gap) is split over laps at the landing, through the
cascade.  For each: the full chain (setter rank, lap, R), which slow readings are on which lap at the landing, and the
perturbation: move the slow group's top reading (the one that left the slow group's lap) by -1 and +1 (readings scaled
by 4 for a finer step) and record where the landing goes and whether the slow group is then on one lap.  Exact."""
import random
from fractions import Fraction as F
from math import floor, exp, log
from collections import Counter
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def chain(T):
    t = F(1, 8 * T[0]); mv = []
    while True:
        W = [d for d in T if nd(d * t) < E8]
        if not W: return t, mv
        ex = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in W}
        t2 = max(ex.values()); a = max(W, key=lambda d: ex[d]); mv.append((T.index(a), floor(a * t2), float(8 * T[0] * t2))); t = t2
def split(T):
    gi = max(range(1, 7), key=lambda i: F(T[i], T[i - 1])); return gi
rng = random.Random(0); found = []
while len(found) < 12:
    dmin = rng.randrange(1, 60); S = rng.uniform(25, 2000)
    xs = sorted({max(dmin + 1, int(round(dmin * exp(rng.uniform(0, log(S)))))) for _ in range(5)} | {dmin, int(dmin * S)})
    if len(xs) != 7: continue
    T = tuple(xs); t, mv = chain(T)
    if t == F(1, 8 * T[0]): continue
    gi = split(T); laps = [floor(d * t) for d in T[:gi]]
    if len(set(laps)) > 1: found.append((T, t, mv, gi, laps))
for T, t, mv, gi, laps in found:
    print("T =", T, " spread %.1f" % (T[-1] / T[0]), " slow group ranks 0..%d, laps at landing %s" % (gi - 1, laps))
    print("   landing R* = %.4f (units d_min); chain (rank, lap, R):" % float(8 * T[0] * t), mv)
    # which slow reading is off the slow group's majority lap, and perturb it
    maj = Counter(laps).most_common(1)[0][0]; off = [i for i, l in enumerate(laps) if l != maj]
    for i in off[:2]:
        for dv in (-1, 1):
            U = [4 * d for d in T]; U[i] += dv; U = tuple(sorted(U))
            if len(set(U)) < 7: continue
            t2, mv2 = chain(U); gi2 = split(U); laps2 = [floor(d * t2) for d in U[:gi2]]
            print("   perturb slow rank %d by %+d/4: R* = %.4f, slow laps %s, moves %d" % (i, dv, float(8 * U[0] * t2), laps2, len(mv2)))
