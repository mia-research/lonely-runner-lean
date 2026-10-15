#!/usr/bin/env python3
"""Observation of BHK case S6 by c = v3/D (v2 = (c-1)D, v3 = cD). For each c:
 (1) runner 2 at runner 3's openings: the opening (k + 1/6)/v3 puts runner 2 at residue
     (c-1)(6k+1) mod 6c, so whether runner 2 is clear there depends only on c and k mod c. Lists the
     usable k mod c (runner 2 clear) -- exact.
 (2) per step of the cascade, which elements are in the way (as size ranks), aggregated by c;
 (3) whether runner 3 is ever a setter, and whether the endpoint is an opening of runner 3.
Reads sets from six_cascade_observe_v1.tsv and re-runs the cascade to record blockers per step."""
from fractions import Fraction as F
from collections import Counter, defaultdict
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c, m, ranks, laps, T, fr = l.rstrip("\n").split("\t")
    if c == "S6": rows.append((eval(s), eval(ranks), int(fr)))
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def blockers_per_step(S, n=6):
    t = F(1, n * S[0]); steps = []
    while True:
        blk = tuple(i + 1 for i, d in enumerate(S) if cd(d * t) < F(1, n))
        steps.append(blk)
        if not blk: return steps
        best = None
        for i, d in enumerate(S):
            if cd(d * t) < F(1, n):
                x = d * t - F(1, n); cc = -((-x.numerator) // x.denominator); o = (cc + F(1, n)) / d
                if best is None or o > best: best = o
        t = best
print("(1) runner 2 clear at runner 3's opening k (k mod c), exact:")
for c in range(2, 13):
    good = [k for k in range(c) if c <= ((c - 1) * (6 * k + 1)) % (6 * c) <= 5 * c]
    print(f"   c={c}: usable k mod c = {good}  ({len(good)} of {c})")
byc = defaultdict(lambda: {"n": 0, "r3set": 0, "end3": 0, "first_blk": Counter(), "r2blk_any": 0})
for S, rk, fr in rows:
    D = S[2] - S[1]; c = S[2] // D; key = min(c, 8)
    b = byc[key]; b["n"] += 1
    b["r3set"] += 3 in rk; b["end3"] += fr == 3
    st = blockers_per_step(S)
    b["first_blk"][st[0]] += 1
    b["r2blk_any"] += any(2 in s for s in st)
print("(2,3) by c:")
for c in sorted(byc):
    b = byc[c]
    print(f"   c={c if c < 8 else '>=8'}: sets={b['n']}; runner 3 ever a setter {b['r3set']}; ends at runner 3 {b['end3']}; "
          f"runner 2 in the way at some step {b['r2blk_any']}; blockers at start {b['first_blk'].most_common(4)}")
