"""Anatomy of the scale cascade chains (recursion from scale_cascade_recursion_v1, unchanged rule).
For each runner with >= 2 changes of scale: the sequence of setters (runner label, reading, lap N), the number of
distinct runners used, and for 2-runner chains whether they strictly alternate.  AP frame: index a_l = round(d_l/m),
deviation e_l = d_l/m - a_l."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
def rnd(x): return floor(x + F(1, 2))
def chain(V, i):
    D = {j: abs(V[j] - V[i]) for j in range(8) if j != i}; m = min(D.values())
    scale = m; seq = []
    while True:
        inway = {}
        for j, d in D.items():
            s = d / scale; N = rnd(s / 8)
            if abs(s - 8 * N) < 1: inway[j] = (s / (8 * N + 1), N)
        if not inway: return m, D, seq
        r = min(v[0] for v in inway.values()); j = min(k for k in inway if inway[k][0] == r)
        seq.append((j, inway[j][1])); scale *= r
def job(V):
    out = []
    for i in range(8):
        m, D, seq = chain(V, i)
        if len(seq) < 2: continue
        labels = [j for j, N in seq]; distinct = sorted(set(labels))
        alt = len(distinct) == 2 and all(labels[k] != labels[k + 1] for k in range(len(labels) - 1))
        idx = {j: rnd(D[j] / m) for j in D}; dev = {j: D[j] / m - idx[j] for j in D}
        out.append(dict(V=V, i=i, n=len(seq), distinct=len(distinct), alt=alt, seq=seq,
                        info={j: (str(D[j] / m), idx[j], str(dev[j])) for j in distinct}))
    return out
def run(name, arrs, pool, show=4):
    R = [x for r in pool.map(job, arrs, chunksize=8) for x in r]
    print(f"\n{name}: chains with >= 2 moves: {len(R)}")
    print("   distinct runners in the chain:", dict(sorted(Counter(x['distinct'] for x in R).items())))
    two = [x for x in R if x["distinct"] == 2]
    print(f"   two-runner chains that strictly alternate A,B,A,B: {sum(x['alt'] for x in two)} of {len(two)}")
    print("   chain length by distinct runners:", dict(sorted(Counter((x['distinct'], x['n']) for x in R).items())))
    for x in R[:show]:
        print(f"   e.g. speeds {[str(v) for v in x['V']]} subject r{x['i']+1}: moves {[(f'r{j+1}', N) for j, N in x['seq']]}; "
              f"runners (d/d_min, AP index, deviation) {x['info']}")
if __name__ == "__main__":
    rng = random.Random(27); AP = [F(k) for k in range(1, 9)]
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
