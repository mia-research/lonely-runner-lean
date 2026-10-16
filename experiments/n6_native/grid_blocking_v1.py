#!/usr/bin/env python3
"""Observation only. How the grids before q* get blocked, in slot / flank terms. At the unit instant c/q runner d reads
x/q, x = d c mod q. It blocks when x/q is within 1/6 of the subject (lap point): ON the subject (x = 0, i.e. q | d; it
then blocks every unit instant of that grid) or NEAR it (0 < x < q/6: just past, entry side; x > 5q/6: just before,
exit side). Mirror c <-> q - c swaps entry and exit side.
Per grid q < q*: whole grid blocked by one ON runner (divisibility), or by NEAR blocks only, or mixed; per blocked
opportunity: the runners blocking it and on which side; at q*: the lonely instants' slot picture x by speed rank.
Sets: primitive SixResidual <= 40, and all primitive 5-sets <= 30 for comparison."""
import math
from itertools import combinations
from collections import Counter
def qstar_detail(S):
    q = 2; grids = []
    while True:
        units = [c for c in range(1, q) if math.gcd(c, q) == 1]
        on = [i for i, d in enumerate(S) if d % q == 0]
        rec = []; lon = []
        for c in units:
            near = [(i, "entry" if 6 * ((d * c) % q) < q else "exit") for i, d in enumerate(S)
                    if (d * c) % q and (6 * ((d * c) % q) < q or 6 * ((d * c) % q) > 5 * q)]
            if not on and not near: lon.append(c)
            rec.append((c, near))
        if lon: return q, grids, [(c, tuple((d * c) % q for d in S)) for c in lon]
        grids.append((q, on, rec)); q += 1
def run(sets, label):
    gkind = Counter(); per_opp = Counter(); near_sides = Counter(); near_rank = Counter(); qs = Counter()
    lonely_slots = Counter(); ongrid = Counter()
    for S in sets:
        q, grids, lon = qstar_detail(S); qs[q] += 1
        for g, on, rec in grids:
            if on:
                gkind["whole grid blocked by a runner on the subject (q | d)"] += 1
                for i in on: ongrid[(g, i + 1)] += 1
            else:
                gkind["blocked by near runners only"] += 1
                for c, near in rec:
                    per_opp[len(near)] += 1
                    for i, side in near: near_sides[side] += 1; near_rank[i + 1] += 1
        for c, xs in lon[:1]:
            lonely_slots[tuple(round(6 * x / q, 2) for x in xs)] += 0  # placeholder kept small
            lonely_slots[(q, tuple(sorted(xs)))] += 1
    print(f"== {label}: sets {len(sets)}; q* {sorted(qs.items())}")
    print("   grids before q*:", dict(gkind))
    print("   grids blocked on the subject, (q, runner rank) commonest:", ongrid.most_common(12))
    print("   near-only grids: runners per unit instant", dict(sorted(per_opp.items())), "; sides", dict(near_sides),
          "; by speed rank", dict(sorted(near_rank.items())))
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
run(rows, "primitive SixResidual <= 40")
allsets = [S for S in combinations(range(1, 31), 5) if math.gcd(*S) == 1]
run(allsets, "all primitive 5-sets <= 30")
