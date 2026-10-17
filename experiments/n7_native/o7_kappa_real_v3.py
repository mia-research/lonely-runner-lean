#!/usr/bin/env python3
"""Exact re-check of o7_kappa_real_v1 / v2 (E4): kappa = v5 W5 on [0, T] for rational speed tuples (Fractions), near
the minimisers (relative perturbations with denominator 10^5) and random rational ratio tuples (v5 = 1)."""
import random, sys
from fractions import Fraction as Fr
from multiprocessing import Pool
S7, S67 = Fr(1, 7), Fr(6, 7)
def W5(P, T):
    cur = None
    for v in P:
        B = []; m = 0
        while (m + S7) / v < T:
            B.append(((m + S7) / v, min((m + S67) / v, T))); m += 1
        if cur is None: cur = B; continue
        i = j = 0; out = []
        while i < len(cur) and j < len(B):
            lo, hi = max(cur[i][0], B[j][0]), min(cur[i][1], B[j][1])
            if hi > lo: out.append((lo, hi))
            if cur[i][1] < B[j][1]: i += 1
            else: j += 1
        cur = out
    return max((h - l for l, h in cur), default=Fr(0))
def near(args):
    base, eps_num, seed = args; rnd = random.Random(seed); out = []
    for _ in range(100):
        P = tuple(v * (1 + Fr(rnd.randint(-eps_num, eps_num), 10**5)) for v in base)
        out.append(max(P) * W5(P, Fr(60)))
    return base, eps_num, min(out), sum(k < Fr(3, 28) for k in out)
def rnd_tuple(args):
    T, seed = args; rnd = random.Random(seed); out = []
    for _ in range(200):
        P = tuple(sorted(Fr(rnd.randint(2000, 99999), 10**5) for _ in range(4))) + (Fr(1),)
        out.append(W5(P, Fr(T)))
    return T, min(out), sum(k < Fr(3, 28) for k in out)
if __name__ == "__main__":
    jobs = [(b, e, 7) for b in [(1, 3, 4, 5, 7), (1, 4, 5, 6, 7), (1, 2, 3, 4, 5)] for e in (1000, 300, 100)]
    with Pool(10) as pool:
        for b, e, mn, nb in pool.map(near, jobs):
            print(f"{b} relative perturbation <= {e}/10^5, 100 rational samples: min kappa {mn} ({float(mn):.4f}); below 3/28: {nb}")
        for T, mn, nb in pool.map(rnd_tuple, [(20, s) for s in range(10)] + [(100, s) for s in range(10)]):
            print(f"random rational ratios (v5 = 1), T = {T}, 200 samples: min kappa {float(mn):.4f} (exact {mn}); below 3/28: {nb}")
