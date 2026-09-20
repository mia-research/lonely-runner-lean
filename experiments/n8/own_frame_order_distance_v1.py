"""Framework coordinates throughout.  Time: isolation_sets_v1 (d_min + lap window + BSM), unchanged.
Labels: for subject i, idx_j = round((v_j - v_i)/d_min(i)) mod 8 (subject = 0) -- the runner's own d_min progression.
Distance: least swaps of track-adjacent runners to the step-1 cycle (AP event r=1,7) or step-3 cycle (r=3,5) in those
labels.  Same BFS and families as global_order_distance_v1 (speed-rank labels), reported side by side."""
import sys, random
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/experiments/n8")
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from global_order_distance_v1 import canon, D1, D3
import isolation_sets_v1 as iso
def fr(x): return x - floor(x)
def rnd(x): return floor(x + F(1, 2))
def dist_of(labels):
    c = canon(labels); d1, d3 = D1[c], D3[c]
    return ("step-1" if d1 <= d3 else "step-3"), min(d1, d3)
def job(V):
    out = []
    for i in range(8):
        _, k, pts, ivs = iso.isolation_set(V, i, lap_cap=400)
        if k is None: continue
        t = sorted(list(pts) + [a for a, b in ivs])[0]
        pos = sorted((fr((v - V[i]) * t), j) for j, v in enumerate(V))
        if any(pos[a][0] == pos[(a + 1) % 8][0] for a in range(8)):
            out.append(("tie on track", None, None)); continue
        order = [j for _, j in pos]
        speed = dist_of(order)
        m = min(abs(V[j] - V[i]) for j in range(8) if j != i)
        lab = {j: rnd((V[j] - V[i]) / m) % 8 for j in range(8)}
        if len(set(lab.values())) < 8:
            out.append(("own-frame slots shared", speed, None)); continue
        own = dist_of([lab[j] for j in order])
        out.append(("ok", speed, own))
    return out
def run(name, arrs, pool):
    rows = [x for r in pool.map(job, [V for V in arrs if V], chunksize=8) for x in r]
    ok = [(s, o) for tag, s, o in rows if tag == "ok"]
    print(f"\n{name}: {len(rows)} runner-times | ties on track {sum(t=='tie on track' for t,_,_ in rows)}"
          f" | own-frame slots shared {sum(t=='own-frame slots shared' for t,_,_ in rows)} | compared {len(ok)}")
    print("   speed-rank labels, swaps:", dict(sorted(Counter(s[1] for s, o in ok).items())))
    print("   own d_min labels,  swaps:", dict(sorted(Counter(o[1] for s, o in ok).items())),
          " step-1/step-3 at 0:", dict(Counter(o[0] for s, o in ok if o[1] == 0)))
    moved = Counter((s[1], o[1]) for s, o in ok if s[1] != o[1])
    print("   (speed-rank swaps -> own-frame swaps) where they differ:", dict(sorted(moved.items())))
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
