#!/usr/bin/env python3
"""Primitive SixResidual sets with few good openings at the largest flank (G <= GMAX), with the
good openings k, the multiplier 6k+1 reduced mod 6e, readings r_d = d(6k+1) mod 6e as fractions of
6e, and additive relations among the elements (x + y = z, x + y = 2z, 2x = y + z). Exact."""
import sys, math, importlib.util
from itertools import combinations
from fractions import Fraction as F
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI, GMAX = int(sys.argv[1]), int(sys.argv[2])
rel_counter = Counter(); n_tight = 0; n_all = 0; rel_all = Counter()
def relations(S):
    out = set()
    for x, y in combinations(S, 2):
        if x + y in S: out.add("x+y=z")
        if (x + y) % 2 == 0 and (x + y) // 2 in S and (x+y)//2 not in (x,y): out.add("x+y=2z")
        if y - x in S and y - x != x: out.add("y-x=w")
    for z in S:
        for x in S:
            if x != z and 2 * x == z: out.add("2x=z")
    return out
shown = 0
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    n_all += 1
    e = S[-1]
    good = [k for k in range(e) if all(e <= (d * (6*k+1)) % (6*e) <= 5*e for d in S)]
    rel = relations(S)
    for x in rel: rel_all[x] += 1
    if 0 < len(good) <= GMAX:
        n_tight += 1
        for x in rel: rel_counter[x] += 1
        if not rel: rel_counter["none"] += 1
        if shown < 25:
            k = good[0]
            rd = {d: F((d*(6*k+1)) % (6*e), 6*e) for d in S}
            print(f"  {S} good k={good} 6k+1={6*k+1} readings={ {d: str(v) for d,v in rd.items()} } rel={sorted(rel)}")
            shown += 1
print(f"HI={HI}: residual={n_all}; tight (1<=G<={GMAX})={n_tight}")
print("  relations among tight sets:", dict(rel_counter))
print("  relations among all residual sets:", dict(rel_all), "(of", n_all, ")")
