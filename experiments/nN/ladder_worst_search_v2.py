"""Targeted search for sets that push the ladder's live-step count k up.

k = number of live lattices in [L_0, D*) (ladder_live_steps_v1).  Random sampling gave k <= 8.
Here: hill-climbing on 7-sets of positive integers (primitive), elements up to 10^12, objective k
(ties broken by D*), moves: replace one element by a random value, by a random multiple of
8*lcm(1..c), or by d +- small; accept if the objective does not decrease.  400 restarts x 4000 steps, fixed
seeds.  Reports the best k found and its set, re-checked by exact circDist at the returned instant.
"""
import random, time
from math import gcd, lcm
from functools import reduce
from fractions import Fraction as F

def clears(S, D, a): return all(D <= d * a % (8 * D) <= 7 * D for d in S)
def dead(S, D): return any(d % (8 * D) == 0 for d in S)
def ladder(S, cap=2000):
    D = 1; L0 = None; k = 0
    while D <= cap:
        if not dead(S, D):
            if L0 is None: L0 = D
            for j in range(D):
                if clears(S, D, 8 * j + 1): return k, D, L0, 8 * j + 1
            k += 1
        D += 1
    return k, D, L0, None
def ok(S): return len(set(S)) == 7 and reduce(gcd, S) == 1
rnd = random.Random(29); HI = 10**12
def mutate(S):
    S = list(S); i = rnd.randrange(7); r = rnd.random()
    if r < 0.4: S[i] = rnd.randrange(1, HI)
    elif r < 0.7: S[i] = 8 * lcm(*range(1, rnd.randrange(2, 13))) * rnd.randrange(1, 200)
    else: S[i] = max(1, S[i] + rnd.randrange(-50, 51))
    return tuple(sorted(S))
t0 = time.time(); best = None
for restart in range(400):
    S = tuple(sorted(rnd.sample(range(1, HI), 7)))
    while not ok(S): S = tuple(sorted(rnd.sample(range(1, HI), 7)))
    cur = ladder(S)
    for step in range(4000):
        T = mutate(S)
        if not ok(T): continue
        v = ladder(T)
        if (v[0], v[1]) >= (cur[0], cur[1]): S, cur = T, v
    if best is None or (cur[0], cur[1]) > (best[1][0], best[1][1]): best = (S, cur)
    if restart % 50 == 49: print(f"  after {restart+1} restarts: best k={best[1][0]}, D*={best[1][1]}, L_0={best[1][2]}  ({time.time()-t0:.0f}s)", flush=True)
S, (k, D, L0, a) = best
print(f"best: k={k}, L_0={L0}, D*={D}, a={a}, S={S}")
if a:
    t = F(a, 8 * D); cd = lambda x: min(x % 1, 1 - x % 1)
    print(f"  exact check at t={t}: min circDist {min(cd(d * t) for d in S)} (>= 1/8: {min(cd(d * t) for d in S) >= F(1, 8)})")
