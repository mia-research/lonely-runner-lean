#!/usr/bin/env python3
"""Closure events along grid-to-S deformations (method of six_deform_v1.py, N steps per speed), over a sample of
residual sets (every K-th set of six_cascade_observe_v1.tsv) plus the 11 resonant chains (six_tau_over_v2.out).
A CLOSURE: the earliest lonely instant's branch changes AND the old instant is now blocked. Records, per closure:
moving runner, the runners blocking the old instant, the new branch's flank, and whether the new flank is the
moving runner, one of the closers, or another runner; and whether the new instant is later or earlier."""
import sys
from fractions import Fraction as F
from collections import Counter
N, K = int(sys.argv[1]), int(sys.argv[2])
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
thr = F(1, 6)
def earliest(V):
    t = F(1, 6 * min(V))
    while True:
        blk = [d for d in V if cd(d * t) < thr]
        if not blk: return t
        t = max((-((-(d * t - thr).numerator) // (d * t - thr).denominator) + thr) / d for d in blk)
def branch(V, t):
    for i, d in enumerate(V):
        x = d * t - thr
        if x.denominator == 1: return (i + 1, int(x))
    return (0, None)
sets = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]][::K]
chains = [tuple(map(int, l.split()[1:6])) for l in open("six_tau_over_v2.out")]
for label, group in (("ordinary sample", sets), ("resonant chains", chains)):
    rel = Counter(); direction = Counter(); closers = Counter(); n_cl = 0; n_relabel = 0
    for S in group:
        V = [F(S[0] * k) for k in range(1, 6)]
        T = earliest(V); B = branch(V, T)
        for idx in (4, 3, 2, 1):
            a, b = V[idx], F(S[idx])
            for j in range(1, N + 1):
                W = list(V); W[idx] = a + (b - a) * F(j, N)
                if len(set(W)) < 5: continue
                T2 = earliest(W); B2 = branch(W, T2)
                if B2 != B:
                    cl = [k + 1 for k, d in enumerate(W) if cd(d * T) < thr]
                    if cl:
                        n_cl += 1
                        mv = idx + 1; nf = B2[0]
                        rel["new flank = moving runner" if nf == mv else ("new flank = a closer" if nf in cl else "new flank = other")] += 1
                        direction["later" if T2 > T else "earlier"] += 1
                        closers[tuple(cl) == (mv,)] += 1
                    else:
                        n_relabel += 1
                T, B = T2, B2
            V[idx] = b
    print(f"{label}: sets {len(group)}; closures {n_cl}; relabelings (new earlier instant, old still lonely) {n_relabel}")
    print(f"   where the isolation reappears: {dict(rel)}")
    print(f"   new instant later/earlier than the closed one: {dict(direction)}")
    print(f"   closed by the moving runner alone: {closers[True]}; by others too: {closers[False]}")
