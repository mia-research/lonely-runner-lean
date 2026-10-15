#!/usr/bin/env python3
"""First move of the cascade at t0 = 1/(6 v1). Rule tested (exact): v_k is in the way at t0 iff
rho_k = v_k / v1 lies in (6m - 1, 6m + 1) for some integer m >= 1; the setter is the in-the-way element
with the latest next opening (6m + 1) / (6 v_k). Compared with the recorded first move in
six_cascade_observe_v1.tsv. Also tabulates, per BHK case, which ranks can be in the way at t0."""
from fractions import Fraction as F
from collections import Counter, defaultdict
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c, m, ranks, laps, T, fr = l.rstrip("\n").split("\t")
    rows.append((eval(s), c, eval(ranks), eval(laps)))
mism = 0; blocked_ranks = defaultdict(Counter)
for S, case, rk, lp in rows:
    v1 = S[0]; cands = []
    for idx, v in enumerate(S):
        rho = F(v, v1)
        m = round(rho / 6)
        if m >= 1 and abs(rho - 6 * m) < 1:
            cands.append((F(6 * m + 1, 6 * v), idx + 1, m))
            blocked_ranks[case][idx + 1] += 1
    pred = max(cands)[1:] if cands else None
    obs = (rk[0], lp[0]) if rk else None
    if pred != obs: mism += 1
print(f"sets={len(rows)}; first-move mismatches between rule and recorded cascade: {mism}")
for case in ("S8", "S5", "S6", "S7"):
    print(f"  {case}: ranks in the way at t0 (count of sets): {dict(sorted(blocked_ranks[case].items()))}")
