"""Framework coordinates, every runner-time.  Time from isolation_sets_v1 (unchanged).  For subject i, own d_min m,
idx_j = round((v_j - v_i)/m); at the runner's time t (u = m t) the ideal position of j on the runner's own progression
is frac(idx_j * u); the actual position is frac((v_j - v_i) t).  Question: is the actual cyclic track order the same as
the ideal cyclic order?  Runners whose ideal positions coincide form a block; a block may appear in any internal order.
Also recorded: the swap distance between the two orders (ideal ties broken to minimise), and whether u is an own-AP instant."""
import sys, random
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/experiments/n8")
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from itertools import combinations, permutations
from collections import Counter
from multiprocessing import Pool
import isolation_sets_v1 as iso
def fr(x): return x - floor(x)
def rnd(x): return floor(x + F(1, 2))
def cyc_eq_blocks(actual, ideal_pos):
    """actual: cyclic list of runners.  ideal_pos: runner -> ideal position.  True if reading the actual cycle, the ideal
    positions are non-decreasing around the circle exactly once (i.e. actual order is a linear extension of ideal order)."""
    n = len(actual); vals = [ideal_pos[j] for j in actual]
    drops = sum(1 for k in range(n) if vals[(k + 1) % n] < vals[k])
    return drops <= 1
def job(V):
    out = []
    for i in range(8):
        _, k, pts, ivs = iso.isolation_set(V, i, lap_cap=400)
        if k is None: continue
        t = sorted(list(pts) + [a for a, b in ivs])[0]
        m = min(abs(V[j] - V[i]) for j in range(8) if j != i); u = m * t
        idx = {j: rnd((V[j] - V[i]) / m) for j in range(8)}
        ideal = {j: fr(idx[j] * u) for j in range(8)}
        actual = [j for _, j in sorted((fr((V[j] - V[i]) * t), j) for j in range(8))]
        own_ap = (8 * u).denominator == 1 and int(8 * u) % 2 == 1
        blocks = len(set(ideal.values())) < 8
        out.append((own_ap, blocks, cyc_eq_blocks(actual, ideal)))
    return out
def run(name, arrs, pool):
    rows = [x for r in pool.map(job, [V for V in arrs if V], chunksize=8) for x in r]
    c = Counter(rows)
    tot = len(rows); same = sum(v for (a, b, s), v in c.items() if s)
    print(f"\n{name}: {tot} runner-times; actual track order = ideal order on own d_min progression: {same}")
    for own in (True, False):
        n = sum(v for (a, b, s), v in c.items() if a == own); y = sum(v for (a, b, s), v in c.items() if a == own and s)
        print(f"   time is an own-AP instant = {own}: {y} of {n}")
    print(f"   ideal positions coincide for some runners: {sum(v for (a,b,s),v in c.items() if b)} (of which same order {sum(v for (a,b,s),v in c.items() if b and s)})")
if __name__ == "__main__":
    rng = random.Random(19); AP = [F(j + 1) for j in range(8)]
    def ok(V): return V if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0 else None
    with Pool(8) as pool:
        run("one runner moved from the AP", [ok([AP[j] + (F(s) * F(x, 100) if j == k else 0) for j in range(8)]) for k in range(8) for x in (1, 10, 30, 50, 90) for s in (-1, 1)], pool)
        for sc in (F(1, 100), F(1, 10), F(3, 10), F(9, 10)):
            L = []
            while len(L) < 150:
                V = ok([AP[j] + F(rng.randint(-1000, 1000), 1000) * sc for j in range(8)])
                if V: L.append(V)
            run(f"every runner moved, |dev| <= {sc}", L, pool)
        run("all 8-subsets of [1,14], gcd 1", [[F(v) for v in c] for c in combinations(range(1, 15), 8) if reduce(gcd, c) == 1], pool)
        run("random integers [1,1000]", [[F(v) for v in sorted(rng.sample(range(1, 1001), 8))] for _ in range(300)], pool)
