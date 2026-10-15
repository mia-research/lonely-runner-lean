#!/usr/bin/env python3
"""Observation only. Owner: there are more possible isolation points than runners can cover.
Isolation points: the openings of each flank b in one period (whole-number speeds, period 1): t = (6k+1)/(6b),
k = 0..b-1, b of them. Runner d blocks opening k iff R = d(6k+1) mod 6b lies outside [b, 5b] (Flanks residue form).
Per flank: b openings; the count each other runner blocks; the sum of those counts (what the runners could cover if
their blocks never coincided); the union (what they do cover); free openings = b - union.
Per set: flanks with sum >= b (enough blocks to cover by count) yet free openings > 0, and the overlap sum - union."""
from collections import Counter
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
def blocked(d, b, k): R = (d * (6 * k + 1)) % (6 * b); return not (b <= R <= 5 * b)
flank_stats = Counter(); per_set = Counter(); ratio = Counter(); free_any = 0; ex = []
for S in rows:
    any_free = False; enough_but_free = 0
    for b in S:
        sets = [set(k for k in range(b) if blocked(d, b, k)) for d in S if d != b]
        s = sum(len(x) for x in sets); u = len(set().union(*sets)); free = b - u
        flank_stats[("count >= openings" if s >= b else "count < openings", "free" if free else "covered")] += 1
        ratio[round(s / b, 1)] += 1
        if free: any_free = True
        if s >= b and free:
            enough_but_free += 1
            if len(ex) < 4: ex.append((S, b, [len(x) for x in sets], s, u, free))
    free_any += any_free
    per_set[enough_but_free > 0] += 1
print(f"sets {len(rows)}; sets with some flank having a free opening: {free_any}")
print("flanks by (sum of individual block counts vs openings, covered or not):")
for k, c in sorted(flank_stats.items()): print(f"  {c:7d}  {k}")
print("sets with a flank where the runners have enough blocks to cover by count, yet an opening is free:", dict(per_set))
print("sum of block counts / openings, distribution (rounded):", sorted(ratio.items())[:25])
for e in ex: print("  example (set, flank b, blocks per other runner, sum, union, free):", e)
