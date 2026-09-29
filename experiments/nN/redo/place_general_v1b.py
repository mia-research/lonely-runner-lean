"""E176 follow-up: the incidents that need a rung with q >= 17, and the 3 not placed (random populations of
place_general_v1, same seed).  Where do they land (R = 8 d_min t*), how many separations from the bound, and which
readings are in the subject's slot at each step?  A reading in the slot at the bound is within d_min of a multiple of
8 d_min (|d - 8 n d_min| < d_min)."""
import random
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from place_general_v1 import classify, move, lonely, E8, cd


def chain(T):
    t = F(1, 8 * T[0]); steps = []
    while True:
        way = [d for d in T if cd(d * t) < E8]
        if not way:
            return steps
        steps.append((t, way))
        t = move(T, t)


def look(T):
    T, ts, n, p = classify(T)
    return T, ts, n, p, chain(T)


if __name__ == '__main__':
    rng = random.Random(11); pops = []
    for top in (48, 96, 200):
        pops.append((top, [tuple(sorted(rng.sample(range(1, top + 1), 7))) for _ in range(30000)]))
    out = open('place_general_v1b.out', 'w'); out.write(__doc__ + "\n")
    with Pool(8) as pool:
        for top, sets in pops:
            rows = pool.map(look, sets, chunksize=500)
            hard = [r for r in rows if r[3][0] == 'none' or (r[3][1] is not None and r[3][1] >= 17)]
            out.write("\n== readings <= %d: q >= 17 or not placed: %d ==\n" % (top, len(hard)))
            out.write("R (8 d_min t*) : %s\n" % dict(sorted(Counter(round(float(8 * r[0][0] * r[1]), 2) for r in hard).items())[:20]))
            out.write("moves from the bound: %s\n" % dict(sorted(Counter(r[2] for r in hard).items())))
            atb = Counter()
            for r in hard:
                T, m = r[0], r[0][0]
                w0 = r[4][0][1] if r[4] else []
                atb[all(abs(d - 8 * round(F(d, 8 * m)) * m) < m for d in w0) and bool(w0)] += 1
            out.write("the readings in the slot at the bound are all within d_min of a multiple of 8 d_min: %s\n" % dict(atb))
            for r in hard[:8]:
                T, m = r[0], r[0][0]
                out.write("   %s  R=%.4f  place %s  steps: %s\n" % (T, float(8 * m * r[1]), r[3],
                          [(round(float(8 * m * t), 4), w) for t, w in r[4]]))
    out.close()
    print(open('place_general_v1b.out').read()[len(__doc__):])
