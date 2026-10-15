#!/usr/bin/env python3
"""Observation of BHK case S6 (D = v3 - v2 divides v3, so v2 = (c-1)D, v3 = cD; D does not divide v1;
3 v1 < v3). Tabulates setter sequences against c = v3/D and against the set of ranks in the way at
t0 = 1/(6 v1). From six_cascade_observe_v1.tsv."""
from fractions import Fraction as F
from collections import Counter, defaultdict
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c, m, ranks, laps, T, fr = l.rstrip("\n").split("\t")
    if c == "S6": rows.append((eval(s), eval(ranks), eval(laps), int(fr)))
def blocked_at_t0(S):
    v1 = S[0]; out = []
    for i, v in enumerate(S):
        rho = F(v, v1); m = round(rho / 6)
        if m >= 1 and abs(rho - 6 * m) < 1: out.append(i + 1)
    return tuple(out)
byc = defaultdict(Counter); byb = defaultdict(Counter); fin_c = defaultdict(Counter)
for S, rk, lp, fr in rows:
    D = S[2] - S[1]; c = S[2] // D
    byc[min(c, 8)][rk] += 1; fin_c[min(c, 8)][fr] += 1
    byb[blocked_at_t0(S)][rk] += 1
print(f"S6 sets: {len(rows)}")
for c in sorted(byc):
    tot = sum(byc[c].values())
    print(f"  c = v3/D = {c if c < 8 else '>=8'}: {tot} sets; final flank {dict(sorted(fin_c[c].items()))}; top sequences {byc[c].most_common(4)}")
print("  by ranks in the way at t0:")
for b, cnt in sorted(byb.items(), key=lambda kv: -sum(kv[1].values()))[:8]:
    print(f"    blocked {b}: {sum(cnt.values())} sets; top sequences {cnt.most_common(3)}")
