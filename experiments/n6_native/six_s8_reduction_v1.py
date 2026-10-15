#!/usr/bin/env python3
"""§8 (v3 <= 3 v1), observation. Hypothesis from the residues: the three slowest are clear at every state
of the walk, so the walk of S equals the walk of the reduced set {v1, v4, v5} (same instants, same
setters). Checks: (a) states at which some of v1, v2, v3 is in the way; (b) whether walk(S) and
walk({v1,v4,v5}) agree (same sequence of instants); (c) the reduced walk's paths, in ratio terms.
Exact Fractions."""
from fractions import Fraction as F
from collections import Counter
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c = l.split("\t")[:2]
    if c == "S8": rows.append(eval(s))
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def walk(S):
    t = F(1, 6 * S[0]); times = [t]; slow_blk = 0
    while True:
        blk = [d for d in S if cd(d * t) < F(1, 6)]
        slow_blk += any(d in S[:3] for d in blk) if len(S) == 5 else 0
        if not blk: return times, slow_blk
        t = max(F(6 * round(d * t) + 1, 6 * d) for d in blk); times.append(t)
agree = 0; slow_states = 0; slow_sets = []; paths = Counter()
for S in rows:
    tf, sb = walk(S)
    tr, _ = walk((S[0], S[3], S[4]))
    agree += tf == tr
    if sb: slow_states += 1; slow_sets.append(S) if len(slow_sets) < 8 else None
    if tf != tr and len(slow_sets) < 8 and S not in slow_sets: slow_sets.append(S)
print(f"§8 sets: {len(rows)}; walk(S) equals walk({{v1,v4,v5}}): {agree}; sets where v1, v2 or v3 is ever in the way: {slow_states}")
print("  exceptions:", slow_sets)
