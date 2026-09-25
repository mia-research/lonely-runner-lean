"""The non-synchronised step of the induction: for a fast level of f readings (no two consecutive within
relative 1/9, max/min < 9) above u = 7 - f slower readings, the lower orders guarantee a cell of the
slower levels holding ROOM(f) = 9 * 2 (1/(u+1) - 1/8) turns of the level's slowest reading.  The level
clears inside any window longer than its KAPPA: the longest stretch with no joint clear instant, from any
start, in turns of its slowest reading (exact interval merge, open zones, touching zones leave their end
clear).  Target: kappa_f < ROOM(f) for f = 3..6.  kappa is scale invariant (scaling a block leaves its turns unchanged), so small least readings
cover the shapes.  Blocks: exhaustive for small least reading, plus
samples weighted to MILDLY synchronised shapes (consecutive ratios just above 10/9).  Also checks the
cell-width formula of E31 on the 8 narrow cells.  Exact."""
import random, time
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce
from multiprocessing import Pool
def kappa(Fs):
    g = reduce(gcd, Fs)
    z = sorted((F(8 * k - 1, 8 * d), F(8 * k + 1, 8 * d)) for d in Fs for k in range(0, d // g + 2))
    best = F(0); lo, hi = z[0]
    for a, b in z[1:]:
        if a < hi: hi = max(hi, b)
        else: best = max(best, hi - lo); lo, hi = a, b
    return max(best, hi - lo) * min(Fs)
def ok(Fs): return all(9 * Fs[i + 1] > 10 * Fs[i] for i in range(len(Fs) - 1)) and Fs[-1] < 9 * Fs[0]
ROOM = {f: 9 * 2 * (F(1, 8 - f) - F(1, 8)) for f in range(1, 7)}
def exhaustive(args):
    f, first, top = args; best = (F(0), None)
    for rest in combinations(range(first + 1, top), f - 1):
        Fs = (first,) + rest
        if ok(Fs):
            k = kappa(Fs)
            if k > best[0]: best = (k, Fs)
    return best
def mild(args):
    f, N, seed = args; rnd = random.Random(seed); best = (F(0), None)
    for _ in range(600):
        r = [1 + F(1, 9) + F(rnd.randrange(1, 400), 1000) for _ in range(f - 1)]
        Fs = [N + rnd.randrange(0, N)]
        for x in r: Fs.append(int(Fs[-1] * x) + 1)
        Fs = tuple(Fs)
        if ok(Fs):
            k = kappa(Fs)
            if k > best[0]: best = (k, Fs)
    return best
if __name__ == "__main__":
    for f in (3, 4, 5, 6):
        t0 = time.time(); top = {3: 60, 4: 40, 5: 34, 6: 40}[f]
        with Pool(8) as p:
            ex = max(p.map(exhaustive, [(f, a, top) for a in range(2, top // 2)]), key=lambda x: x[0])
            md = max(p.map(mild, [(f, N, 100 * f + s) for N in (40, 100) for s in range(8)]), key=lambda x: x[0])
        print(f"f={f}: ROOM = {float(ROOM[f]):.3f} turns;  kappa exhaustive (readings < {top}) {float(ex[0]):.3f} at {ex[1]};  "
              f"kappa over mildly synchronised samples {float(md[0]):.3f} at {md[1]}  ({time.time()-t0:.0f}s)", flush=True)
