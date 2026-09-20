"""Do cascade depth and the ratio t/(1/(8 d_min)) stay bounded as families are pushed?  Cascade recursion only (exact, fast);
the recursion equals BSM on every family tested so far (items 27, 29).  Reported: max depth, max ratio, and where."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import gcd
from functools import reduce
from itertools import combinations
from multiprocessing import Pool
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from scale_cascade_recursion_v1 import cascade
def job(V):
    best = (0, 0, None)
    for i in range(len(V)):
        scale, last, steps, D = cascade(V, i)
        m = min(D.values()); ratio = m / scale          # t / bound = (1/(8 scale)) / (1/(8 m))
        if (steps + 1, ratio) > best[:2]: best = (steps + 1, ratio, i)
    return best, V
def run(name, arrs, pool):
    res = pool.map(job, arrs, chunksize=16)
    md = max(res, key=lambda x: x[0][0]); mr = max(res, key=lambda x: x[0][1])
    print(f"{name}: {len(arrs)} arrangements | max scales {md[0][0]} at {[str(v) for v in md[1]]} r{md[0][2]+1} | "
          f"max t/bound {float(mr[0][1]):.3f} at {[str(v) for v in mr[1]]} r{mr[0][2]+1}", flush=True)
if __name__ == "__main__":
    rng = random.Random(32)
    with Pool(8) as pool:
        for hi in (16, 20, 24):
            run(f"all 8-subsets of [1,{hi}], gcd 1", [[F(v) for v in c] for c in combinations(range(1, hi + 1), 8) if reduce(gcd, c) == 1], pool)
        for X in (200, 1000, 5000):
            run(f"push-out families x <= {X}", [[F(v) for v in V] for x in range(8, X + 1) for V in [(1,2,3,4,5,6,7,x),(1,2,3,4,5,6,x-1,x),(1,2,3,4,5,x-2,x-1,x)] if len(set(V)) == 8 and sorted(V) == list(V)], pool)
        for hi in (100, 1000, 10000, 100000):
            run(f"random integers [1,{hi}] (20000 arrangements)", [[F(v) for v in sorted(rng.sample(range(1, hi + 1), 8))] for _ in range(20000)], pool)
