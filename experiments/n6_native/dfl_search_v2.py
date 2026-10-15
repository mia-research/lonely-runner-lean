#!/usr/bin/env python3
"""v2 (residual only, n = 6): as dfl_search_v1.py, but a state counts only if it is a primitive SixResidual set.
Directed search for large tau = d_min * T, T the cascade's fixed point from 1/(n d_min) (DoorFirstLap is
tau <= 1). Exact Fractions. Hill-climbing with restarts: state = sorted tuple of n-1 distinct positive ints;
moves change one element by a step from a Fibonacci-like set or rescale one element; accept if tau does not
decrease (ties allowed, to drift on plateaus); seeds = the top sets of an exhaustive small range plus random.
Usage: dfl_search_v1.py n SEED_RANGE ITERS RESTARTS RNG_SEED
Prints the best tau found with its set and move count; a positive control is the run at n = 8."""
import sys, random
from fractions import Fraction as F
from itertools import combinations
n, SR, ITERS, RESTARTS, SEED = map(int, sys.argv[1:6])
import importlib.util, math
spec = importlib.util.spec_from_file_location('r', 'six_residual_v1.py')
RM = importlib.util.module_from_spec(spec); spec.loader.exec_module(RM)
def ok(S): return math.gcd(*S) == 1 and RM.six_residual(tuple(S))
rng = random.Random(SEED)
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def tau(S, cap=5000):
    m = min(S); t = F(1, n * m); thr = F(1, n); moves = 0
    while moves < cap:
        blk = [d for d in S if cd(d * t) < thr]
        if not blk: return m * t, moves
        t = max((-((-(d * t - thr).numerator) // (d * t - thr).denominator) + thr) / d for d in blk)
        moves += 1
    return None, moves
# seeds: exhaustive over (n-1)-subsets of [1, SR], keep the top 30 by tau
pool = []
for S in combinations(range(1, SR + 1), n - 1):
    if not ok(S): continue
    tv, mv = tau(S)
    if tv is not None: pool.append((tv, S))
pool.sort(reverse=True)
seeds = [S for _, S in pool[:30]]
print(f"n={n}: exhaustive [1,{SR}] max tau = {pool[0][0]} = {float(pool[0][0]):.4f} at {pool[0][1]}", flush=True)
steps = [1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144]
best = (pool[0][0], pool[0][1], 0)
for r in range(RESTARTS):
    S = list(rng.choice(seeds))
    cur, _ = tau(tuple(sorted(S)))
    if cur is None: continue
    for it in range(ITERS):
        T2 = list(S); i = rng.randrange(n - 1)
        if rng.random() < 0.15:
            T2[i] = max(1, int(T2[i] * rng.choice([2, 3, F(3, 2), F(2, 3), F(1, 2)])))
        else:
            T2[i] = max(1, T2[i] + rng.choice([-1, 1]) * rng.choice(steps))
        if len(set(T2)) != n - 1: continue
        T2 = sorted(T2)
        if not ok(T2): continue
        val, mv = tau(tuple(T2))
        if val is None: continue
        if val >= cur:
            S, cur = T2, val
            if val > best[0]:
                best = (val, tuple(T2), mv)
                print(f"  restart {r} iter {it}: tau = {val} = {float(val):.4f} at {tuple(T2)} ({mv} moves)", flush=True)
print(f"BEST n={n}: tau = {best[0]} = {float(best[0]):.5f} at {best[1]} ({best[2]} moves); tau > 1: {best[0] > 1}")
