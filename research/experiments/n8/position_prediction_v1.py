"""Test of POSITION_PREDICTION_v1 Q1-Q3 against BSM moments.  Exact Fractions."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import floor, ceil
from itertools import combinations
from functools import reduce
from math import gcd
from collections import Counter
from multiprocessing import Pool
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from full_transit_positions_v2 import first_time
def fr(x): return x - floor(x)
def cd(x): x = fr(x); return min(x, 1 - x)
def lonely(V, i, t): return all(cd((V[j] - V[i]) * t) >= F(1, 8) for j in range(8) if j != i)
def next_opening(D, t):
    """least (8k+1)/(8D) >= t"""
    k = ceil((8 * D * t - 1) / 8)
    return F(8 * max(k, 0) + 1, 8) / D
def job(V):
    out = []
    for i in range(8):
        ds = {j: abs(V[j] - V[i]) for j in range(8) if j != i}; m = min(ds.values())
        b = F(1, 8) / m
        t = first_time(V, i)
        if t == b: out.append(("at bound",)); continue
        inway = [j for j in ds if cd(ds[j] * b) < F(1, 8)]
        q1 = max(next_opening(ds[j], b) for j in inway)
        rec = ["displaced", q1 == t, lonely(V, i, q1), t < q1]
        s = {j: ds[j] / m for j in ds}
        sharers = [j for j in ds if s[j].denominator == 1 and s[j].numerator % 8 == 0]
        if len(sharers) == 1 and inway == sharers:
            rec.append(t == b + 1 / (8 * ds[sharers[0]]))
        else: rec.append(None)
        out.append(tuple(rec))
    return out
def run(name, arrs, pool):
    rows = [x for r in pool.map(job, arrs, chunksize=8) for x in r]
    d = [r for r in rows if r[0] == "displaced"]
    print(f"\n{name}: {len(rows)} runners, displaced {len(d)}")
    print(f"   Q1/Q2  moment = latest first-opening of the runners in the way at the bound: {sum(r[1] for r in d)}")
    print(f"          ... that time is a lonely time: {sum(r[2] for r in d)};  moment EARLIER than it: {sum(r[3] for r in d)}")
    q3 = [r[4] for r in d if r[4] is not None]
    print(f"   Q3     single wrap partner and nothing else in the way: {len(q3)}, moment = 1/(8 d_min) + 1/(8 D): {sum(q3)}")
if __name__ == "__main__":
    rng = random.Random(23); AP = [F(k) for k in range(1, 9)]
    def ok(V): return V if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0 else None
    fams = []
    fams.append(("one runner moved from the AP, step 0.05", [V for V in (ok([AP[j] + (F(x, 20) - AP[k] if j == k else 0) for j in range(8)]) for k in range(8) for x in range(20 * k + 1, 20 * (k + 2))) if V]))
    L = []
    for sc in (F(1, 10), F(3, 10), F(9, 10)):
        n = 0
        while n < 100:
            V = ok([AP[j] + F(rng.randint(-100, 100), 100) * sc for j in range(8)])
            if V: L.append(V); n += 1
    fams.append(("every runner moved, |dev| <= 0.1, 0.3, 0.9", L))
    fams.append(("spread/push-out integer families x = 8..60", [[F(v) for v in V] for x in range(8, 61) for V in [(1,2,3,4,5,6,7,x),(1,2,3,4,5,6,x-1,x),(1,2,3,4,5,x-2,x-1,x)] if len(set(V)) == 8 and sorted(V) == list(V)]))
    fams.append(("all 8-subsets of [1,14], gcd 1", [[F(v) for v in c] for c in combinations(range(1, 15), 8) if reduce(gcd, c) == 1]))
    fams.append(("random integers [1,500]", [[F(v) for v in sorted(rng.sample(range(1, 501), 8))] for _ in range(400)]))
    with Pool(8) as pool:
        for name, arrs in fams: run(name, arrs, pool)
