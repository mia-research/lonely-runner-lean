"""Before certifying the non-synchronised step: its uniform form needs EVERY starting phase, not only the
phases a small whole-number block reaches on its own orbit (room_vs_kappa_v1 measured the latter).
Full-phase kappa: for readings a_1 = 1 < a_2 < ... < a_f (consecutive ratio >= 10/9, max < 9) and phases
phi in [0,1)^f, the first s >= 0 with every ||phi_i + a_i s|| >= 1/8 (a shifted cascade: move to the
largest next opening of the readings in the way), in turns of a_1.  Exact rationals.  Random shapes and
phases, then local search (perturb phases and ratios, keep the worse) toward the maximum; compared with
ROOM(f)."""
import random, time
from fractions import Fraction as F
from math import floor
from multiprocessing import Pool
def ndist(x): x = x % 1; return min(x, 1 - x)
def first_clear(a, phi, cap=100000):
    s = F(0); n = 0
    while n < cap:
        way = [i for i in range(len(a)) if ndist(phi[i] + a[i] * s) < F(1, 8)]
        if not way: return s
        s = max((F(floor(phi[i] + a[i] * s - F(1, 8)) + 1) + F(1, 8) - phi[i]) / a[i] for i in way); n += 1
    return None
ROOM = {f: 18 * (F(1, 8 - f) - F(1, 8)) for f in range(1, 7)}
def shape(rnd, f):
    while True:
        a = [F(1)]
        for _ in range(f - 1): a.append(a[-1] * (F(10, 9) + F(rnd.randrange(0, 3000), 1000)))
        if a[-1] < 9: return a
def work(args):
    f, seed = args; rnd = random.Random(seed); best = (F(0), None, None)
    for _ in range(40):
        a = shape(rnd, f); phi = [F(rnd.randrange(1000), 1000) for _ in range(f)]
        v = first_clear(a, phi)
        for it in range(150):                        # local search toward a longer blocked stretch
            b = [x if i == 0 else max(a[i - 1] * F(10, 9), min(x * (1 + F(rnd.randrange(-20, 21), 1000)), F(89, 10))) for i, x in enumerate(a)]
            b = sorted(b); b = [b[0]] + [max(b[i], b[i - 1] * F(10, 9)) for i in range(1, f)]
            if b[-1] >= 9: continue
            q = [(x + F(rnd.randrange(-30, 31), 1000)) % 1 for x in phi]
            w = first_clear(b, q)
            if w is not None and w >= v: a, phi, v = b, q, w
        if v > best[0]: best = (v, a, phi)
    return best
if __name__ == "__main__":
    for f in (3, 4, 5, 6):
        t0 = time.time()
        with Pool(8) as p: parts = p.map(work, [(f, 1000 * f + s) for s in range(8)])
        v, a, phi = max(parts, key=lambda x: x[0])
        print(f"f={f}: ROOM {float(ROOM[f]):.3f};  full-phase kappa found {float(v):.3f} turns  "
              f"(shape {[round(float(x), 3) for x in a]}, phases {[round(float(x), 3) for x in phi]})  ({time.time()-t0:.0f}s)", flush=True)
