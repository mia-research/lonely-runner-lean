#!/usr/bin/env python3
"""CLUSTER + OUTLIER: choose the grid to fit the tuple.  Exact Fraction, no float.

A cluster is a subset C with max C <= 7 min C.  On the OPEN window
    W = ( 1/(8 min C), 7/(8 max C) ),   |W| = (7 min C - max C)/(8 min C max C) > 0
every e in C has e*t strictly inside (1/8, 7/8), so ||e t|| > 1/8.  One line, no LRC.
(C = E is the bounded-ratio theorem; the content is C a proper subset.)

Each outlier v has bad-set components of length 1/(4v) at period 1/v, so it meets at most
floor(|W| v) + 1 of them:

   CLUSTER CRITERION:  sum over outliers of (floor(|W| v)+1)/(4v)  <  |W|   =>  witness.

The optimal C is a CONTIGUOUS run of the sorted speeds (max/min <= 7 is an interval
condition), so 21 candidates per tuple.  Compared here against the LRC-derived window
eta = (1/(h+1) - 1/8)/max(H) used in BOX_AND_INTERVAL_DEFICIENCY_v1.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce
import sys

LVL = F(1, 8)
def nrm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1 - f)

def cluster_windows(T):
    """all (C, lo, hi) with C a contiguous run and max C <= 7 min C, window non-empty."""
    out = []
    for i in range(7):
        for j in range(i, 7):
            C = T[i:j + 1]
            m, M = C[0], C[-1]
            if M > 7 * m: continue
            lo, hi = F(1, 8 * m), F(7, 8 * M)
            if lo < hi: out.append((C, lo, hi))
    return out

def cluster_crit(T):
    """returns (C, W, witness t) if the criterion fires, else None."""
    best = None
    for C, lo, hi in cluster_windows(T):
        L = hi - lo
        out = [v for v in T if v not in C]
        budget = sum(F(int(L * v) + 1, 4 * v) for v in out)
        if budget < L:
            # exhibit the witness: remove the outliers' bad sets from W, exactly
            cuts = []
            for v in out:
                for k in range(int(lo * v) - 1, int(hi * v) + 2):
                    cuts.append((F(k, v) - LVL / v, F(k, v) + LVL / v))
            cuts.sort()
            cur = lo
            t = None
            for a, b in cuts:
                if a > cur: t = (cur + min(a, hi)) / 2; break
                cur = max(cur, b)
                if cur >= hi: break
            if t is None and cur < hi: t = (cur + hi) / 2
            if t is not None and best is None: best = (C, L, t)
    return best

def lrc_window_len(T, H):
    h = len(H)
    if not (1 <= h <= 6): return None
    return 2 * (F(1, h + 1) - LVL) / max(H)

def run(box=20, cap=1200):
    tuples = [T for T in combinations(range(1, box + 1), 7)
              if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
    step = max(1, len(tuples) // cap)
    tuples = tuples[::step]
    fired = ok = 0
    better = 0
    resid = []
    for T in tuples:
        r = cluster_crit(T)
        if r is None: resid.append(T); continue
        C, L, t = r
        fired += 1
        if all(nrm(F(e) * t) > LVL for e in T): ok += 1
        else: print(f"    FALSIFIED T={T} C={C} t={t}")
        Lr = lrc_window_len(T, [e for e in T if e in C])
        if Lr is not None and L > Lr: better += 1
    n = len(tuples)
    print(f"Case-2 sample from [1..{box}] (every {step}th): {n} tuples")
    print(f"  cluster criterion fires                  : {fired}  ({100*fired//n}%)")
    print(f"  witness verified exactly against all 7   : {ok}   "
          f"{'ALL OK' if ok == fired else 'FAILURES'}")
    print(f"  cluster window LONGER than the LRC window: {better} / {fired}")
    print(f"  residue                                  : {len(resid)}  "
          f"({100*len(resid)//n}%)")
    print(f"  first residual tuples: {resid[:6]}")
    return set(resid)

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 20)
