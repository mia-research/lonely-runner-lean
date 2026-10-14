"""Link test: a neighbour tie (runners j,k coinciding beside runner i at i's own time) vs the scale jump.
For each tie: does j or k need a scale jump (dead lattice prediction P > 1)?  And conversely: for each runner
that needs a jump, does some other runner see it inside a neighbour tie at that runner's time?"""
import sys, random
from fractions import Fraction as F
from functools import reduce
from math import gcd
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/experiments/n8")
    from scale_jump_battery_v1 import least_L, predicted_L, sides
def job(V):
    P = [predicted_L(V, i) for i in range(8)]
    L = [least_L(V, i) for i in range(8)]
    c = Counter(); seen = set()
    for i in range(8):
        Li, u, m = L[i]
        if Li is None: continue
        b, a = sides(V, i, u / m)
        for grp in (a, b):
            if len(grp) > 1:
                c["neighbour ties"] += 1
                jumpers = [j for j in grp if P[j] > 1]
                c["tie contains a runner needing a jump"] += bool(jumpers)
                c["tie is a slot-sharing pair (difference = 8q x its d_min)"] += any(
                    (abs(V[j] - V[k]) / min(abs(V[j] - V[x]) for x in range(8) if x != j)).denominator == 1 and
                    (abs(V[j] - V[k]) / min(abs(V[j] - V[x]) for x in range(8) if x != j)).numerator % 8 == 0
                    for j in grp for k in grp if j != k)
                seen |= set(jumpers)
    for j in range(8):
        if P[j] > 1:
            c["runners needing a jump"] += 1
            c["  ... seen inside some neighbour tie"] += j in seen
    return c
if __name__ == "__main__":
    rng = random.Random(18)
    fams = [("all 8-subsets of [1,16], gcd 1", [tuple(F(v) for v in cc) for cc in combinations(range(1, 17), 8) if reduce(gcd, cc) == 1]),
            ("random [1,100]", [tuple(F(v) for v in sorted(rng.sample(range(1, 101), 8))) for _ in range(1500)]),
            ("random [1,1000]", [tuple(F(v) for v in sorted(rng.sample(range(1, 1001), 8))) for _ in range(400)])]
    with Pool(8) as pool:
        for name, arrs in fams:
            tot = sum(pool.map(job, arrs, chunksize=16), Counter())
            print(f"{name}: {dict(tot)}")
