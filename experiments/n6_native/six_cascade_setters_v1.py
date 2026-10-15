#!/usr/bin/env python3
"""Observation only, from six_cascade_observe_v1.tsv. Per BHK case (S8, S5, S6, S7):
  - the most common setter sequences (size ranks) with their lap sequences;
  - the first setter and its lap;
  - the final displacement measured as v1*T (the reading of the slowest element at the endpoint),
    reported as floor(6*v1*T) (which sixth-of-lap the slowest element ends in) and whether v1*T < 1.
No rates are offered as mechanisms; counts are descriptive."""
from fractions import Fraction as F
from collections import Counter, defaultdict
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c, m, ranks, laps, T, fr = l.rstrip("\n").split("\t")
    rows.append((eval(s), c, eval(ranks), eval(laps), F(T)))
for case in ("S8", "S5", "S6", "S7"):
    R = [x for x in rows if x[1] == case]
    seq = Counter(tuple(zip(rk, lp)) for _, _, rk, lp, _ in R)
    seq_ranks = Counter(rk for _, _, rk, _, _ in R)
    first = Counter((rk[0], lp[0]) for _, _, rk, lp, _ in R if rk)
    sixth = Counter()
    for S, _, rk, lp, T in R:
        x = S[0] * T
        sixth[int(6 * x) if x < 1 else "lap>=1"] += 1
    print(f"== {case}: {len(R)} sets")
    print("  setter-rank sequences:", seq_ranks.most_common(8))
    print("  sequences with laps:", seq.most_common(8))
    print("  first move (setter rank, lap):", first.most_common(8))
    print("  slowest element's reading at the end, v1*T: sixth-of-lap ->", dict(sorted(sixth.items(), key=str)))
