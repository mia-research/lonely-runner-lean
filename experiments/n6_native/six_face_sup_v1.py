#!/usr/bin/env python3
"""E26: (1) the box holding the 18 real late configurations outside (1,3,4,5,7) (from six_tau_climb_v1.out);
(2) the supremum of tau just across the spread-5 face: climb with r5 = 5 + eps fixed, eps in {1e-2, 1e-3, 1e-4},
r2, r3, r4 free. Exact cascade."""
import random, ast
from fractions import Fraction as F
src = open("six_tau_climb_v1.py").read().split("tops = [")[0]
import sys; sys.argv = ["x", "0", "0", "0"]; ns = {}; exec(src, ns); tau = ns["tau"]; lapv = ns["lapv"]
line = open("six_tau_climb_v1.out").read().split("outside box (1,3,4,5,7): 18 ")[1]
for r, t in ast.literal_eval(line.strip()):
    r = [F(x) for x in r]; print("  outlier laps", lapv(r, F(t)), "tau", float(F(t)))
rng = random.Random(3)
def rnd(x): return F(round(x * 10**7), 10**7)
for eps in (F(1, 100), F(1, 1000), F(1, 10000)):
    r5 = 5 + eps; best = F(0); bestr = None
    for st in range(40):
        r = [F(1)] + sorted(rnd(rng.uniform(1.5, 4.9)) for _ in range(3)) + [r5]
        if st == 0: r = [F(1), rnd(2.3957), rnd(2.8958), rnd(3.81), r5]
        cur = tau(r); step = 0.05
        for it in range(1500):
            mid = sorted(rnd(float(x) * (1 + rng.uniform(-step, step))) for x in r[1:4])
            cand = [F(1)] + mid + [r5]
            if cand[1] <= 1 or cand[3] >= r5 or len(set(cand)) < 5: continue
            tv = tau(cand)
            if tv >= cur: r, cur = cand, tv
            elif it % 150 == 149: step = max(step * 0.6, 1e-6)
        if cur > best: best, bestr = cur, r
    print(f"r5 = 5 + {eps}: sup tau found {float(best):.6f} = {best} at {[float(x) for x in bestr]}, laps {lapv(bestr, best)}")
    print("    entry instants of the laps:", [float((6*k+1)/(6*x)) for k, x in zip(lapv(bestr, best), bestr)])
