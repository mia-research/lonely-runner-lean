"""Is 'actual order = ideal order at own-AP instants' forced?  At each own-AP instant runner-time record:
all deviations zero (then forced); the largest displacement |dev_j * t| mod-1 distance, in eighths (slot = 1/8)."""
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
def rnd(x): return floor(x + F(1, 2))
def cd(x): x = fr(x); return min(x, 1 - x)
def job(V):
    out = []
    for i in range(8):
        _, k, pts, ivs = iso.isolation_set(V, i, lap_cap=400)
        if k is None: continue
        t = sorted(list(pts) + [a for a, b in ivs])[0]
        m = min(abs(V[j] - V[i]) for j in range(8) if j != i); u = m * t
        if not ((8 * u).denominator == 1 and int(8 * u) % 2 == 1): continue
        dev = [(V[j] - V[i]) - rnd((V[j] - V[i]) / m) * m for j in range(8)]
        if all(d == 0 for d in dev): out.append("all deviations zero (forced)"); continue
        mx = max(cd(d * t) for d in dev) * 8          # in slots
        out.append("largest displacement < 1/2 slot" if mx < F(1, 2) else "some runner displaced >= 1/2 slot")
    return out
def run(name, arrs, pool):
    print(name, dict(Counter(x for r in pool.map(job, [V for V in arrs if V], chunksize=8) for x in r)))
if __name__ == "__main__":
    rng = random.Random(19); AP = [F(j + 1) for j in range(8)]
    def ok(V): return V if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0 else None
    with Pool(8) as pool:
        for sc in (F(1, 10), F(3, 10), F(9, 10)):
            L = []
            while len(L) < 150:
                V = ok([AP[j] + F(rng.randint(-1000, 1000), 1000) * sc for j in range(8)])
                if V: L.append(V)
            run(f"every runner moved |dev|<={sc}:", L, pool)
        run("all 8-subsets of [1,14]:", [[F(v) for v in c] for c in combinations(range(1, 15), 8) if reduce(gcd, c) == 1], pool)
        run("random integers [1,1000]:", [[F(v) for v in sorted(rng.sample(range(1, 1001), 8))] for _ in range(300)], pool)
