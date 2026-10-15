#!/usr/bin/env python3
"""E31 independent check: at the residual sets themselves (every 4th in [1,40]; no deformation), the open lonely
boxes in [0, 2/d_1] (positive length). Pairs differing by one lap of one runner r: count, r's rank, whether r is
the fastest, and for each pair J (the other four's common interval) in laps of r. Also: boxes with no such
neighbour. Usage: six_neighbours_static_v1.py K"""
import sys
from fractions import Fraction as F
from collections import Counter
src = open("six_boxes_v1.py").read().split("K = int(sys.argv[1])")[0]
ns = {}; exec(src, ns)
s6 = F(1, 6)
def floor(x): return x.numerator // x.denominator
def open_boxes(V, W):
    ivs = [((F(0), W), ())]
    for v in V:
        new = []
        for (a, b), lab in ivs:
            k = max(floor(a * v - s6) - 1, 0)
            while True:
                l, r = (k + s6) / v, (k + 5 * s6) / v
                if l > b: break
                L, R = max(a, l), min(b, r)
                if L < R: new.append(((L, R), lab + (k,)))
                k += 1
        ivs = new
    return [lab for _, lab in ivs]
K = int(sys.argv[1])
sets = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]][::K]
nbox = Counter(); pairs_r = Counter(); lonely_box = Counter(); Jr = Counter(); fast = Counter(); tot = 0
for S in sets:
    V = [F(x) for x in S]; B = open_boxes(V, F(2, S[0]))
    tot += 1; nbox[min(len(B), 12)] += 1
    Bs = set(B); has_nb = Counter()
    for b in B:
        for r in range(5):
            nb = tuple(b[i] + (1 if i == r else 0) for i in range(5))
            if nb in Bs:
                pairs_r[r + 1] += 1; has_nb[b] += 1; has_nb[nb] += 1
                fast["r fastest" if r == 4 else "r not fastest"] += 1
                others = [i for i in range(5) if i != r]
                J0 = max((6*b[i]+1)/(6*V[i]) for i in others); J1 = min((6*b[i]+5)/(6*V[i]) for i in others)
                Jr[min(round(float((J1 - J0) * V[r]), 1), 3.0)] += 1
    for b in B: lonely_box["has a one-lap neighbour" if has_nb[b] else "no one-lap neighbour"] += 1
print(f"residual sets: {tot}; open boxes in [0, 2/d1] per set (12 = 12+): {dict(sorted(nbox.items()))}")
print("  one-lap neighbour pairs by runner r:", dict(sorted(pairs_r.items())), dict(fast))
print("  boxes:", dict(lonely_box))
print("  |J| in laps of r for the pairs (3.0 = 3+):", dict(sorted(Jr.items())))
