"""The moment iteration written as a cascade of AP scales.
   D_0 = d_min.  At scale D, reading s_l = d_l / D; in the way iff |s_l - 8 N_l| < 1 (N_l = nearest integer to s_l/8).
   D_{n+1} = D_n * min over in-the-way l of s_l / (8 N_l + 1).   Stop when no reading is within 1 of a multiple of 8.
   Time = 1/(8 D_final).   Checked against BSM (full_transit_positions_v2.first_time, unchanged).
Also recorded at the final scale: the last runner's reading (= 8k+1), its speed rank relative to the subject, and whether it is
the subject's speed-neighbour; and the number of scales."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from full_transit_positions_v2 import first_time
def rnd(x): return floor(x + F(1, 2))
def cascade(V, i):
    D = {j: abs(V[j] - V[i]) for j in range(8) if j != i}
    scale = min(D.values()); last = min(D, key=lambda j: D[j]); steps = 0
    while True:
        inway = {}
        for j, d in D.items():
            s = d / scale; N = rnd(s / 8)
            if abs(s - 8 * N) < 1: inway[j] = s / (8 * N + 1)
        if not inway: return scale, last, steps, D
        r = min(inway.values()); last = min(j for j in inway if inway[j] == r)
        scale = scale * r; steps += 1
def job(V):
    out = []
    for i in range(8):
        scale, last, steps, D = cascade(V, i)
        t = 1 / (8 * scale); b = first_time(V, i)
        s_last = D[last] / scale
        out.append(dict(ok=(t == b), steps=steps, last_reading=s_last,
                        last_is_speed_nb=abs(last - i) == 1, last_rank=min(abs(last - i), 8 - abs(last - i))))
    return out
def run(name, arrs, pool):
    R = [x for r in pool.map(job, arrs, chunksize=8) for x in r]
    moved = [x for x in R if x["steps"] > 0]
    print(f"\n{name}: {len(R)} runners | cascade time = BSM: {sum(x['ok'] for x in R)} | scales used: {dict(sorted(Counter(x['steps']+1 for x in R).items()))}")
    print(f"   last runner's reading at the final scale: {dict(Counter(str(x['last_reading']) for x in R).most_common(6))}")
    print(f"   cascaded runners (>=1 change of scale), last runner = speed-neighbour: {sum(x['last_is_speed_nb'] for x in moved)} of {len(moved)};"
          f" its speed-rank distance: {dict(sorted(Counter(x['last_rank'] for x in moved).items()))}")
if __name__ == "__main__":
    rng = random.Random(26); AP = [F(k) for k in range(1, 9)]
    def ok(V): return V if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0 else None
    fams = [("one runner moved, step 0.01", [V for V in (ok([AP[j] + (F(x, 100) - AP[k] if j == k else 0) for j in range(8)]) for k in range(8) for x in range(100 * k + 1, 100 * (k + 2))) if V])]
    L = []
    while len(L) < 600:
        V = ok([AP[j] + F(rng.randint(-900, 900), 1000) for j in range(8)])
        if V: L.append(V)
    fams.append(("every runner moved, |dev| <= 0.9", L))
    fams.append(("all 8-subsets of [1,16], gcd 1", [[F(v) for v in c] for c in combinations(range(1, 17), 8) if reduce(gcd, c) == 1]))
    fams.append(("random integers [1,1000]", [[F(v) for v in sorted(rng.sample(range(1, 1001), 8))] for _ in range(500)]))
    with Pool(8) as pool:
        for n, a in fams: run(n, a, pool); sys.stdout.flush()
