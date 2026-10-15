#!/usr/bin/env python3
"""E26: adversarial climb on tau = d_min*T over REAL (rational, denominators up to 10^6) configurations
rho = (1, r2, r3, r4, r5), sorted. Exact cascade for T. Random multiplicative steps, accept if tau does not
decrease; step shrinks on stagnation. Starts: random in spread [4.5, 8] plus the 16 top integer sets.
Reports the best tau found, its lap vector, and for every late configuration met (tau >= 7/6) whether the box
(1,3,4,5,7) is alive. Usage: six_tau_climb_v1.py starts iters seed"""
import sys, random
from fractions import Fraction as F
starts, iters, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
s6 = F(1, 6)
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def tau(r):
    t = s6
    for _ in range(10000):
        blk = [d for d in r if cd(d * t) < s6]
        if not blk: return t
        t = max((((d * t - s6).numerator // (d * t - s6).denominator) + 1 + s6) / d for d in blk)
    return None
K0 = (1, 3, 4, 5, 7)
def alive(r, k): return all((6*k[i]+1)*r[j] <= (6*k[j]+5)*r[i] for i in range(5) for j in range(5) if i != j)
def lapv(r, t): return tuple(int((x*t*6 - 1) // 6) for x in r)
tops = [(23,54,68,89,117),(14,34,42,55,72),(17,41,51,67,88),(21,51,64,84,110),(20,49,61,80,105),(19,46,58,76,100),(10,25,32,42,55),(9,23,29,38,50)]
best = (F(0), None); late = 0; late_out = []; maxlap = 0
def rnd(x): return F(round(x * 10**6), 10**6)
for st in range(starts):
    if st < len(tops): r = [F(x, tops[st][0]) for x in tops[st]]
    else:
        r5 = rng.uniform(4.5, 8); r = sorted([1.0] + [rng.uniform(1, r5) for _ in range(3)] + [r5]); r = [F(1)] + [rnd(x) for x in r[1:]]
    cur = tau(r); step = 0.05
    for it in range(iters):
        cand = [F(1)] + sorted(rnd(float(x) * (1 + rng.uniform(-step, step))) for x in r[1:])
        if cand[1] <= 1 or len(set(cand)) < 5: continue
        tv = tau(cand)
        if tv is None: continue
        if tv >= F(7, 6):
            late += 1
            if not alive(cand, K0): late_out.append((tuple(str(x) for x in cand), str(tv)))
        maxlap = max(maxlap, int((tv*6 - 1)//6))
        if tv >= cur: r, cur = cand, tv
        elif it % 200 == 199: step = max(step * 0.7, 1e-5)
    if cur > best[0]: best = (cur, r)
print(f"starts {starts}, iters {iters}: best tau = {best[0]} = {float(best[0]):.5f} at {[float(x) for x in best[1]]}")
print(f"  lap vector at best: {lapv(best[1], best[0])}; max slowest-runner lap seen: {maxlap}")
print(f"  late configurations evaluated (tau >= 7/6): {late}; outside box (1,3,4,5,7): {len(late_out)}", late_out[:5])
