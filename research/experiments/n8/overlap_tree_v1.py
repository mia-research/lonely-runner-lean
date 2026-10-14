"""Hunter-Kounias on the bad-set overlaps: does the max spanning tree reach 4.5?

|union A_i| <= sum|A_i| - max over spanning trees of sum |A_i ^ A_j|.  Forcing a gap in [1,7]
needs the covered measure below 6, i.e. the tree sum above 10.5 - 6 = 4.5.  Exact rationals.
"""
from fractions import Fraction as F
from itertools import combinations
import random

def bad(s, n=8):
    iv, m = [], 1
    while F(n*m - 1, s) < n - 1:
        a, b = max(F(n*m-1, s), F(1)), min(F(n*m+1, s), F(n-1))
        if b > a: iv.append((a, b))
        m += 1
    return iv

def meas(iv): return sum(b - a for a, b in iv)
def inter(x, y):
    return [(lo, hi) for a, b in x for c, d in y
            for lo, hi in [(max(a, c), min(b, d))] if hi > lo]

rng = random.Random(20260919)
tot_single = tot_pair = F(0); npair = 0
best = F(0); worst = F(10**6)
for _ in range(400):
    S = sorted(rng.sample(range(2, 200), 7))
    B = {s: bad(s) for s in S}
    for s in S: tot_single += meas(B[s])
    pw = {}
    for s, t in combinations(S, 2):
        v = meas(inter(B[s], B[t])); pw[(s, t)] = v; tot_pair += v; npair += 1
    par = {s: s for s in S}
    def find(a):
        while par[a] != a: par[a] = par[par[a]]; a = par[a]
        return a
    tree = F(0)
    for (s, t), v in sorted(pw.items(), key=lambda kv: -kv[1]):
        ra, rb = find(s), find(t)
        if ra != rb: par[ra] = rb; tree += v
    best, worst = max(best, tree), min(worst, tree)

print("400 random 7-reading profiles from [2,200], exact rational arithmetic\n")
print(f"  mean single-reading bad measure : {float(tot_single/(400*7)):.4f}")
print(f"  mean pairwise overlap           : {float(tot_pair/npair):.4f}")
print(f"  max-spanning-tree overlap sum   : min {float(worst):.4f}, max {float(best):.4f}")
print(f"  needed to force a gap           : > 4.5")
print(f"  best Hunter-Kounias bound       : {float(F(21,2) - best):.4f}   vs the 6 needed")
