#!/usr/bin/env python3
"""Phase 2: the T5 region with the fastest runner folded. For a 5-prefix P = (v1..v5), W5(P) = longest interval with
all five in band [1/7, 6/7] (float band intersection, EPS 1e-12). Folding v6: any v6 with v6 W5(P) >= 2/7 closes the
set (runner 6 sweeps an arc of length >= 2/7, which meets the closed band). So the T5-by-v6 region is
   v6 >= 2 / (7 W5(P)),
and W5 scales as W5(cP) = W5(P)/c. Scale-free form: kappa(P) = v5 W5(P) in (0, 5/7]; then v6 >= (2/(7 kappa)) v5 closes.
Reports, over all 5-prefixes <= H (not only primitive, since P need not be primitive):
 - min kappa and its minimisers (normalised by gcd), distribution of kappa;
 - the ratio rho(P) = 2/(7 kappa(P)): the T5 region is v6/v5 >= rho(P)."""
import math, sys
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
exec(open("o7_map_v1.py").read().split("def run(")[0])
def W5(P):
    return max((U - L for L, U in block(P, range(5))), default=0.0)
def work(args):
    v1, H = args; out = []
    for rest in combinations(range(v1 + 1, H + 1), 4):
        P = (v1,) + rest
        if math.gcd(*P) != 1: continue
        out.append((P[4] * W5(P), P))
    out.sort(); return out[:40], Counter(round(k * 49, 0) / 49 for k, _ in out) if False else Counter(min(int(k * 70), 50) for k, _ in out), len(out)
if __name__ == "__main__":
    H = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    with Pool(10) as pool: res = pool.map(work, [(v1, H) for v1 in range(1, H - 3)], chunksize=1)
    low = sorted(x for r in res for x in r[0])[:40]; hist = Counter(); n = 0
    for r in res: hist += r[1]; n += r[2]
    print(f"primitive 5-prefixes <= {H}: {n}")
    print(f"   min kappa = v5 W5 = {low[0][0]:.6f} at {low[0][1]}; rho = 2/(7 kappa) = {2 / (7 * low[0][0]):.4f}")
    print("   40 smallest kappa:", [(round(k, 5), P) for k, P in low])
    print("   kappa histogram, bins of 1/70:", sorted(hist.items()))
