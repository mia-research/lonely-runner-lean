"""REDO of five_cell_floor_v1/v2 (which enumerated 5-element difference sets): the longest lonely cell at
1/8 of a runner with five readings, times its largest reading -- over EVERY runner of every arrangement
of 6 distinct speeds in [1,B] with gcd of differences 1 (runners whose readings collide to fewer than
five are skipped, they are order five).  Exact integer components (BSM rule)."""
import sys
from itertools import combinations
from math import gcd, lcm
from functools import reduce
from fractions import Fraction as F
from multiprocessing import Pool
B = int(sys.argv[1]) if len(sys.argv) > 1 else 30
def longest(ds):
    L = reduce(lcm, ds); M = 8 * L
    z = sorted(((8 * m - 1) * (L // d), (8 * m + 1) * (L // d)) for d in ds for m in range(0, d + 1))
    best = 0; cur = 0
    for a, b in z:
        if a > cur and cur > 0: best = max(best, a - cur)
        cur = max(cur, b)
    return F(best, M)
def work(first):
    out = []
    for rest in combinations(range(first + 1, B + 1), 5):
        V = (first,) + rest
        if reduce(gcd, [v - first for v in rest]) != 1: continue
        for k in range(6):
            ds = sorted({abs(v - V[k]) for v in V if v != V[k]})
            if len(ds) < 5: continue
            out.append((longest(ds) * max(ds), tuple(ds), V, k))
    return sorted(out)[:40]
if __name__ == "__main__":
    with Pool(8) as p: parts = p.map(work, range(1, B - 4))
    allv = sorted(x for part in parts for x in part)
    seen = []; 
    for v, ds, V, k in allv:
        if ds not in [s for _, s, _, _ in seen]: seen.append((v, ds, V, k))
    print(f"arrangements of 6 speeds in [1,{B}], every runner with five readings: least (longest cell x max reading):")
    for v, ds, V, k in seen[:6]:
        print(f"   {v} = {float(v):.5f}: readings {list(ds)}, e.g. runner at speed {V[k]} of {V}")
