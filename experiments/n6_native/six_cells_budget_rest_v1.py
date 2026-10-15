#!/usr/bin/env python3
"""E42: residual sets with no lonely opening at any divisible flank: which flanks carry lonely openings there
(by d mod 6 and by speed rank), and the per-row budget at their divisible flanks (is every row's blocked-shift
total >= 6 by the cost law, so that only overlaps could free a cell)."""
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
def clear(d, e, j): r = d * (6 * j + 1) % (6 * e); return e <= r <= 5 * e
def lonely_at(S, b): return any(all(clear(d, b, j) for d in S) for j in range(b))
cls = Counter(); rank = Counter(); n = 0; costrow = Counter(); freecell_rows = Counter()
for r in rows:
    S = eval(r[0])
    divs = [d for d in S if d % 6 == 0]
    if any(lonely_at(S, e) for e in divs):
        # rows where a cell is free although the cost total is >= 6: freed by overlap
        for e in divs:
            E = e // 6
            for i in range(E):
                tot = sum(sum(1 for u in range(6) if not clear(d, e, u * E + i)) for d in S if d != e)
                free = any(all(clear(d, e, u * E + i) for d in S) for u in range(6))
                if free: freecell_rows["free row, blocked total >= 6 (overlap)" if tot >= 6 else "free row, blocked total < 6 (budget)"] += 1
        continue
    n += 1
    lon = [b for b in S if lonely_at(S, b)]
    cls[tuple(sorted({b % 6 for b in lon}))] += 1
    rank[tuple(sorted(S.index(b) + 1 for b in lon))] += 1
print(f"residual sets with no lonely opening at a divisible flank: {n}")
print("  residues mod 6 of the flanks that do carry lonely openings:", dict(cls.most_common(10)))
print("  speed ranks of those flanks:", dict(rank.most_common(10)))
print("free rows at divisible flanks (sets that have one), budget vs overlap:", dict(freecell_rows))
