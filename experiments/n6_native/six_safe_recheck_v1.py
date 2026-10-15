#!/usr/bin/env python3
"""E41: recheck the two-window coverage of E39 with the exact SAFE test (six_safe_exact_v1.py). Same sets (§5 sets
without a single long-enough J123 window), same pairs (J123 windows within one period, up to three apart). For each
set: covered iff some pair is exactly SAFE. Also compares, for every pair the grid (N = 600) called SAFE, the exact
verdict, and reports disagreements with their failing witness (c, s0-interval)."""
import math, sys
import numpy as np
from fractions import Fraction as F
from collections import Counter
src = open("six_two_window_v1.py").read().split("rows = [l.rstrip")[0]
sys.argv = ["x", "600"]; G = {}; exec(src, G)
E = {}; exec(open("six_safe_exact_v1.py").read().split('if __name__ == "__main__":')[0], E)
safe_grid, safe_exact, clear_ivs, Lform = G["safe"], E["safe_exact"], G["clear_ivs"], G["Lform"]
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
cov = Counter(); dis = Counter(); exs = []; unc = []; npairs = 0
for r in rows:
    if r[1] != "S5": continue
    S = [F(x) for x in eval(r[0])]; g = math.gcd(*[int(x) for x in S]); P = F(1, g)
    ivs = [(F(0), 2 * P)]
    for d in S[:3]: ivs = [iv for a, b in ivs for iv in clear_ivs(d, a, b)]
    rho = S[4] / S[3]
    if max((S[3] * (b - a) for a, b in ivs), default=0) >= Lform(rho): continue
    W = [w for w in ivs if w[0] < P]
    found = False
    for i in range(len(W)):
        for j in range(i + 1, min(i + 4, len(W) + 2)):
            a1, b1 = W[i]; a3, b3 = W[j % len(W)]
            if j >= len(W): a3, b3 = a3 + P, b3 + P
            al, be, ga = S[3]*(b1 - a1), S[3]*(a3 - b1), S[3]*(b3 - a3)
            gs, _ = safe_grid(float(al), float(be), float(ga), float(rho))
            ex, wit = safe_exact(al, be, ga, rho); npairs += 1
            if gs != ex:
                dis[("grid SAFE, exact not" if gs else "exact SAFE, grid not")] += 1
                if len(exs) < 4 and gs: exs.append((tuple(int(x) for x in S), i, j, str(wit[0]), [str(x) for x in wit[1]]))
            if ex: found = True; break
        if found: break
    cov["covered (exact)" if found else "not covered (exact)"] += 1
    if not found: unc.append(tuple(int(x) for x in S))
print("sets:", dict(cov))
print("pairs tested:", npairs, "; grid/exact disagreements:", dict(dis))
for e in exs: print("  grid-SAFE pair with an exact failing start:", e)
print("not covered:", unc)
