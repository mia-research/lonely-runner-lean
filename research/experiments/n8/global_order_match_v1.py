"""At each runner's framework time (isolation_sets_v1, unchanged), take the cyclic track order of all 8 runners
(labels = speed rank 0..7) and classify its 8 adjacent pairs by index step |i-j| mod 8 in {1,2,3,4}.
AP global events: r = 1,7 -> all 8 steps are 1 (the step-1 cycle); r = 3,5 -> all 8 steps are 3 (the step-3 cycle).
Pairs at the same position (ties) are counted separately."""
import sys, random
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/experiments/n8")
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
import isolation_sets_v1 as iso
def fr(x): return x - floor(x)
def steps(V, t):
    pos = sorted((fr(v * t), j) for j, v in enumerate(V))
    out = []; ties = 0
    for k in range(8):
        (p1, a), (p2, b) = pos[k], pos[(k + 1) % 8]
        if p1 == p2: ties += 1; continue
        d = (b - a) % 8; out.append(min(d, 8 - d))
    return Counter(out), ties
def classify(c, ties):
    if ties: return "has a tie"
    if c[1] == 8: return "step-1 cycle (AP r=1,7)"
    if c[3] == 8: return "step-3 cycle (AP r=3,5)"
    if c[1] + c[3] == 8: return "mixture of steps 1 and 3 only"
    return "contains steps 2 or 4"
def job(V):
    res = []
    for i in range(8):
        _, k, pts, ivs = iso.isolation_set(V, i, lap_cap=400)
        if k is None: continue
        t = sorted(list(pts) + [a for a, b in ivs])[0]
        c, ties = steps(V, t)
        res.append((classify(c, ties), tuple(sorted(c.items()))))
    return res
def run(name, arrs, pool, show=4):
    arrs = [V for V in arrs if V]
    rows = [x for r in pool.map(job, arrs, chunksize=8) for x in r]
    cls = Counter(a for a, _ in rows); prof = Counter(b for a, b in rows if a == "contains steps 2 or 4" or a == "mixture of steps 1 and 3 only")
    print(f"\n{name}: {len(rows)} runner-times")
    for k, v in cls.most_common(): print(f"   {k}: {v}")
    if prof: print("   commonest step profiles among the rest ((step, count) over the 8 pairs):", prof.most_common(show))
if __name__ == "__main__":
    rng = random.Random(19)
    AP = [F(j + 1) for j in range(8)]
    def ok(V): return V if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0 else None
    with Pool(8) as pool:
        run("r2 sweep (1, s, 3..8), s = 1.01..1.91", [[F(1), F(101 + 10*k, 100)] + AP[2:] for k in range(10)], pool)
        run("r8 sweep (1..7, s), s = 8.5..16.5", [AP[:7] + [F(x, 2)] for x in range(17, 34)], pool)
        run("one runner moved from the AP (each runner, +-0.01..0.9)",
            [ok([AP[j] + (F(s) * F(x, 100) if j == k else 0) for j in range(8)]) for k in range(8) for x in (1, 10, 30, 50, 90) for s in (-1, 1)], pool)
        for sc in (F(1, 100), F(1, 10), F(3, 10), F(9, 10)):
            L = []
            while len(L) < 150:
                V = ok([AP[j] + F(rng.randint(-1000, 1000), 1000) * sc for j in range(8)])
                if V: L.append(V)
            run(f"every runner moved, |dev| <= {sc}", L, pool)
        run("all 8-subsets of [1,14], gcd 1", [[F(v) for v in c] for c in combinations(range(1, 15), 8) if reduce(gcd, c) == 1], pool)
        run("random integers [1,1000]", [[F(v) for v in sorted(rng.sample(range(1, 1001), 8))] for _ in range(300)], pool)
