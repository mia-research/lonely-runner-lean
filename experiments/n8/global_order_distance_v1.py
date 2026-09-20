"""Distance of each observed cyclic track order from the AP global orders: the least number of swaps of two
track-adjacent runners turning it into the step-1 cycle (r=1,7) or the step-3 cycle (r=3,5).  Cyclic orders are
taken up to rotation and reflection; BFS over all 2520 of them.  Orders with ties are excluded."""
import sys, random
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/experiments/n8")
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from itertools import combinations
from collections import Counter, deque
from multiprocessing import Pool
import isolation_sets_v1 as iso
def canon(seq):
    n = len(seq); best = None
    for s in (seq, seq[::-1]):
        k = s.index(0); c = tuple(s[k:] + s[:k])
        best = c if best is None or c < best else best
    return best
def bfs(targets):
    dist = {t: 0 for t in targets}; q = deque(targets)
    while q:
        x = q.popleft(); L = list(x)
        for k in range(8):
            y = L[:]; y[k], y[(k + 1) % 8] = y[(k + 1) % 8], y[k]; c = canon(y)
            if c not in dist: dist[c] = dist[x] + 1; q.append(c)
    return dist
STEP1 = canon([(j) % 8 for j in range(8)]); STEP3 = canon([(3 * j) % 8 for j in range(8)])
D1 = bfs([STEP1]); D3 = bfs([STEP3])
def fr(x): return x - floor(x)
def job(V):
    out = []
    for i in range(8):
        _, k, pts, ivs = iso.isolation_set(V, i, lap_cap=400)
        if k is None: continue
        t = sorted(list(pts) + [a for a, b in ivs])[0]
        pos = sorted((fr(v * t), j) for j, v in enumerate(V))
        if any(pos[a][0] == pos[(a + 1) % 8][0] for a in range(8)): out.append(("tie", None)); continue
        c = canon([j for _, j in pos]); d1, d3 = D1[c], D3[c]
        out.append(("step-1" if d1 <= d3 else "step-3", min(d1, d3)))
    return out
def run(name, arrs, pool):
    rows = [x for r in pool.map(job, [V for V in arrs if V], chunksize=8) for x in r]
    c = Counter((a, b) for a, b in rows if a != "tie")
    by = Counter(b for a, b in rows if a != "tie")
    print(f"{name}: {len(rows)} runner-times, ties {sum(1 for a,_ in rows if a=='tie')}")
    print("   swaps to nearest AP order:", dict(sorted(by.items())), "  | nearest is step-1 / step-3:",
          {k: v for k, v in sorted(c.items())})
if __name__ == "__main__":
    print("max possible swap distance:", max(D1.values()), "(step-1)", max(D3.values()), "(step-3); orders total", len(D1))
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
    rnd = Counter(min(D1[canon(p)], D3[canon(p)]) for p in [rng.sample(range(8), 8) for _ in range(20000)])
    print("baseline, uniformly random cyclic orders:", dict(sorted(rnd.items())))
