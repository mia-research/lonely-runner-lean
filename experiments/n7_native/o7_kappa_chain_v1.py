#!/usr/bin/env python3
"""Phase 3a: how far elementary native lemmas take kappa = v5 W5 towards 3/28, on integer 5-prefixes <= H.
Chain bound: pick a block B of k runners (any subset, k = 1..5). Native order k+1 gives an instant with B at distance
>= 1/(k+1), so B stays in band [1/7, 6/7] on a window of length W = 2 (1/(k+1) - 1/7) / max(B).  Fold the other
runners in one at a time (ascending, then descending; best kept): a runner of speed u sweeps an arc of length uW, and
the worst-case longest in-band sub-arc is f(uW) with
   f(l) = 0 (l <= 2/7),  (l - 2/7)/2 (2/7 <= l <= 12/7),  5/7 (l >= 12/7),
so the window becomes f(uW)/u.  kappa_chain(P) = v5 * best final window.  For k = 5 this is the proved 1/21.
Reports the share of prefixes with kappa_chain >= 3/28 and the ratio profile of the rest."""
import math, sys
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
def f(l):
    if l <= 2 / 7: return 0.0
    if l <= 12 / 7: return (l - 2 / 7) / 2
    return 5 / 7
def chain(P):
    best = 0.0
    for k in range(1, 6):
        for B in combinations(range(5), k):
            W0 = 2 * (1 / (k + 1) - 1 / 7) / P[B[-1]]
            rest = [i for i in range(5) if i not in B]
            for order in (rest, rest[::-1]):
                W = W0
                for i in order:
                    W = f(P[i] * W) / P[i]
                    if W <= 0: break
                best = max(best, W)
    return P[4] * best
def work(args):
    v1, H = args; c = Counter(); bad = []
    for rest in combinations(range(v1 + 1, H + 1), 4):
        P = (v1,) + rest
        if math.gcd(*P) != 1: continue
        k = chain(P); ok = k >= 3 / 28 - 1e-12; c[ok] += 1
        if not ok:
            c[("r54", min(int(P[4] / P[3] * 4) / 4, 3))] += 1
            if len(bad) < 5: bad.append((round(k, 4), P))
    return c, bad
if __name__ == "__main__":
    H = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    with Pool(10) as pool: res = pool.map(work, [(v1, H) for v1 in range(1, H - 3)], chunksize=1)
    c = Counter(); bad = []
    for r in res: c += r[0]; bad += r[1]
    n = c[True] + c[False]
    print(f"primitive 5-prefixes <= {H}: {n}; chain bound >= 3/28: {c[True]} ({c[True] / n:.2%}); below: {c[False]}")
    print("   below, by v5/v4 (bins of 1/4, capped 3):", sorted((k[1], v) for k, v in c.items() if isinstance(k, tuple)))
    print("   examples below:", sorted(bad)[:25])
