#!/usr/bin/env python3
"""E46: which (residue s, phase a) of runners faster than the flank block the event shifts {1,5} at SixResidual's
divisible flanks, and the shape that results (in CRT terms: s = 3 -> a parity layer, s = 2, 4 -> a mod-3 column,
s = 1, 5 -> one point per layer). Also: at the 1,560 flanks where E45's separation holds, how many runners are
faster than the flank."""
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
def clear(d, e, j): r = d * (6 * j + 1) % (6 * e); return e <= r <= 5 * e
tally = Counter(); fast_at_sep = Counter()
for r in rows:
    S = eval(r[0])
    for e in [d for d in S if d % 6 == 0]:
        E = e // 6
        blk = {d: {u for u in range(6) if not clear(d, e, u * E)} for d in S if d != e}
        sep = all(not (u in b and d % 6 not in (1, 5)) for d, b in blk.items() for u in (1, 5)) and \
              all(not (u in b and d % 6 in (1, 5)) for d, b in blk.items() for u in (2, 3, 4))
        if sep: fast_at_sep[sum(1 for d in blk if d > e)] += 1
        for d, b in blk.items():
            if d > e and d % 6 in (2, 3, 4) and (b & {1, 5}):
                tally[(d % 6, (d // e) % 6, tuple(sorted(b)))] += 1
print("faster zero-divisor runners blocking an event: (s, a, blocked shifts):")
for k, v in tally.most_common(12): print("  ", v, k)
print("flanks where E45's separation holds, by number of runners faster than the flank:", dict(sorted(fast_at_sep.items())))
