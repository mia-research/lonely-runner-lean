#!/usr/bin/env python3
"""Observation only. Owner: the push cannot go on for ever because there are finitely many runners. Measured: in each
forward knot chain (knot_chain_v1's rule, from m + e_J), how many knots each runner holds, i.e. how many extra laps
each runner takes before the next isolation; the largest per runner; and how many distinct runners hold knots."""
import sys
from fractions import Fraction as F
from collections import Counter
import importlib.util
sp = importlib.util.spec_from_file_location("sd", "slot_deform_v1.py"); sd = importlib.util.module_from_spec(sp); sp.loader.exec_module(sd)
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
STEP = int(sys.argv[1]) if len(sys.argv) > 1 else 4
def flanks(v, m):
    ent = [(F(6 * m[i] + 1, 6) / v[i], i) for i in range(5)]; ex = [(F(6 * m[i] + 5, 6) / v[i], i) for i in range(5)]
    L = max(ent)[0]; R = min(ex)[0]
    return [i for x, i in ent if x == L], [i for x, i in ex if x == R]
maxper = Counter(); holders = Counter(); total = Counter(); who = Counter(); n = 0; ex = []
for S in rows[::STEP]:
    R = sd.run_path(S, Counter(), Counter())
    for (m, a, hi), _ in zip(R["segs"], R["segs"][1:]):
        if hi == 0: continue
        v = sd.vs(S, hi); Is, Js = flanks(v, m)
        if len(Is) != 1 or len(Js) != 1: continue
        n += 1
        k = list(m); k[Js[0]] += 1
        while True:
            bad = set(j for i in range(5) for j in range(5) if i != j and (6 * k[i] + 1) * v[j] > (6 * k[j] + 5) * v[i])
            if not bad: break
            for j in bad: k[j] += 1
        g = [k[i] - m[i] for i in range(5)]
        maxper[max(g)] += 1; holders[sum(x > 0 for x in g)] += 1; total[sum(g)] += 1
        for i in range(5):
            if g[i] > 1: who[(i + 1, g[i])] += 1
        if max(g) >= 3 and len(ex) < 3: ex.append((S, hi, m, tuple(g)))
print(f"deaths: {n}")
print("largest number of knots held by one runner in the chain:", dict(sorted(maxper.items())))
print("runners holding at least one knot:", dict(sorted(holders.items())))
print("total knots (extra laps) in the chain:", dict(sorted(total.items())))
print("runners holding more than one knot (speed rank, knots):", who.most_common(10))
for e in ex: print("  example (set, s, dying laps, extra laps per runner):", e)
