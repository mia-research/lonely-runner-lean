"""COMPLETE_PREDICTOR_v1 §1, exactly as documented, against BSM (full_transit_positions_v2.first_time, unchanged):
   m = d_min;  t <- 1/(8m);  while some runner is in the way at t:  t <- max over those runners of their next opening
   (8k+1)/(8d) > t ... (>= t is equivalent: a runner in the way is not at an opening);  re-test.
Records agreement and the number of moves."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import floor, ceil, gcd
from functools import reduce
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from full_transit_positions_v2 import first_time
def fr(x): return x - floor(x)
def cd(x): x = fr(x); return min(x, 1 - x)
def next_opening(d, t):
    k = ceil((8 * d * t - 1) / 8)
    return F(8 * max(k, 0) + 1, 8 * d)
def predictor(V, i, cap=10000):
    ds = [abs(V[j] - V[i]) for j in range(8) if j != i]
    t = F(1, 8) / min(ds); steps = 0
    while True:
        inway = [d for d in ds if cd(d * t) < F(1, 8)]
        if not inway: return t, steps
        t = max(next_opening(d, t) for d in inway); steps += 1
        if steps > cap: return None, steps
def job(V):
    return [(predictor(V, i), first_time(V, i)) for i in range(8)]
def run(name, arrs, pool):
    rows = [x for r in pool.map(job, arrs, chunksize=8) for x in r]
    agree = sum(1 for (t, s), b in rows if t == b)
    print(f"{name}: {len(rows)} runners | predictor = BSM: {agree} | moves: {dict(sorted(Counter(s for (t, s), b in rows).items()))}")
if __name__ == "__main__":
    rng = random.Random(24); AP = [F(k) for k in range(1, 9)]
    def ok(V): return V if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0 else None
    fams = [("one runner moved, step 0.01", [V for V in (ok([AP[j] + (F(x, 100) - AP[k] if j == k else 0) for j in range(8)]) for k in range(8) for x in range(100 * k + 1, 100 * (k + 2))) if V]),
            ("two runners moved (pair grid, step 0.1)", []),
            ("every runner moved, |dev| <= 0.9", []),
            ("push-out and spread families x = 8..200", [[F(v) for v in V] for x in range(8, 201) for V in [(1,2,3,4,5,6,7,x),(1,2,3,4,5,6,x-1,x),(1,2,3,4,5,x-2,x-1,x)] if len(set(V)) == 8 and sorted(V) == list(V)]),
            ("all 8-subsets of [1,16], gcd 1", [[F(v) for v in c] for c in combinations(range(1, 17), 8) if reduce(gcd, c) == 1]),
            ("random integers [1,1000]", [[F(v) for v in sorted(rng.sample(range(1, 1001), 8))] for _ in range(500)])]
    from ok_pair_sweep_v1 import grid
    fams[1] = (fams[1][0], [V for a, b in combinations(range(1, 9), 2) for va in grid(a) for vb in grid(b)
                            for V in [ok([AP[j] if j + 1 not in (a, b) else (va if j + 1 == a else vb) for j in range(8)])] if V])
    L = []
    while len(L) < 600:
        V = ok([AP[j] + F(rng.randint(-900, 900), 1000) for j in range(8)])
        if V: L.append(V)
    fams[2] = (fams[2][0], L)
    with Pool(8) as pool:
        for name, arrs in fams: run(name, arrs, pool); sys.stdout.flush()
