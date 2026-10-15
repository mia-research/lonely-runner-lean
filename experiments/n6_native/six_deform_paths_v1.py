#!/usr/bin/env python3
"""Displacement paths at closures (grid-to-S deformations as in six_deform_stats_v1.py). At each closure, run the
cascade on the new configuration starting from the closed instant T_old; record the path (setter rank, lap) until
the first lonely instant, check that it ends at the new earliest lonely instant, and tabulate: number of steps,
whether the first setter is the moving runner, and the setter pattern after it (relative to the moving runner:
same, slower, faster). Sample: every K-th residual set plus the 11 resonant chains."""
import sys
from fractions import Fraction as F
from collections import Counter
N, K = int(sys.argv[1]), int(sys.argv[2])
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
thr = F(1, 6)
def step(V, t):
    blk = [d for d in V if cd(d * t) < thr]
    if not blk: return None, None, None
    best = max(((-((-(d * t - thr).numerator) // (d * t - thr).denominator) + thr) / d, d) for d in blk)
    return best[0], best[1], blk
def earliest(V):
    t = F(1, 6 * min(V))
    while True:
        nt, _, _ = step(V, t)
        if nt is None: return t
        t = nt
sets = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]][::K]
chains = [tuple(map(int, l.split()[1:6])) for l in open("six_tau_over_v2.out")]
for label, group in (("ordinary sample", sets), ("resonant chains", chains)):
    nsteps = Counter(); first_is_mover = Counter(); after = Counter(); agree = 0; n = 0
    for S in group:
        V = [F(S[0] * k) for k in range(1, 6)]
        T = earliest(V)
        for idx in (4, 3, 2, 1):
            a, b = V[idx], F(S[idx])
            for j in range(1, N + 1):
                W = list(V); W[idx] = a + (b - a) * F(j, N)
                if len(set(W)) < 5: continue
                T2 = earliest(W)
                if T2 != T and any(cd(d * T) < thr for d in W):
                    n += 1; t = T; path = []
                    while True:
                        nt, setter, blk = step(W, t)
                        if nt is None: break
                        path.append(W.index(setter)); t = nt
                    agree += t == T2
                    nsteps[min(len(path), 6)] += 1
                    first_is_mover[path[0] == idx] += 1
                    rel = tuple("same" if p == idx else ("slower" if p < idx else "faster") for p in path[1:])
                    after[rel[:3]] += 1
                T = T2
            V[idx] = b
    print(f"{label}: closures {n}; cascade from the closed instant ends at the new earliest instant: {agree}")
    print(f"   steps to settle (6 = 6 or more): {dict(sorted(nsteps.items()))}")
    print(f"   first setter is the moving runner: {first_is_mover[True]}; another: {first_is_mover[False]}")
    print(f"   setters after the first, relative to the moving runner (first three): {after.most_common(8)}")
