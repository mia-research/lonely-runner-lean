#!/usr/bin/env python3
"""Exact re-check of o7_t5_v1 / o7_t5_v2 (E3): kappa(P) = v5 W5(P) over primitive 5-prefixes <= H, exact integers
(o7_exact; kappa = v5 * Wscaled / (7 M) as a Fraction). Reports min kappa, its minimisers and every prefix with
kappa < 5/28, and the count at kappa = 5/28."""
import math, sys
from fractions import Fraction as Fr
from itertools import combinations
from multiprocessing import Pool
from o7_exact import W_scaled
def work(args):
    v1, H = args; low = []; at = 0; mn = None
    for rest in combinations(range(v1 + 1, H + 1), 4):
        P = (v1,) + rest
        if math.gcd(*P) != 1: continue
        W, M = W_scaled(P); k = Fr(P[4] * W, 7 * M)
        if mn is None or k < mn[0]: mn = (k, P)
        if k < Fr(5, 28): low.append((k, P))
        elif k == Fr(5, 28): at += 1
    return mn, low, at
if __name__ == "__main__":
    H = int(sys.argv[1])
    with Pool(10) as pool: res = pool.map(work, [(v1, H) for v1 in range(1, H - 3)], chunksize=1)
    mn = min(r[0] for r in res if r[0]); low = sorted(x for r in res for x in r[1]); at = sum(r[2] for r in res)
    print(f"exact, primitive 5-prefixes <= {H}: min kappa {mn[0]} at {mn[1]}; kappa < 5/28: {len(low)}; kappa = 5/28: {at}")
    for k, P in low: print(f"   {P}: kappa {k}, rho {Fr(2, 7) / k}")
