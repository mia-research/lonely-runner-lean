#!/usr/bin/env python3
"""E42: the shift budget at the finer cell scale, on SixResidual sets in [1,40] (six_cascade_observe_v1.tsv).
At a divisible flank e = 6E in S, openings j < e are written j = u*E + i (u < 6 coarse shift, i < E cell).
Opening j is lonely iff every d in S has e <= d(6j+1) mod 6e <= 5e (Flanks.clear_at_int_flank_iff_emod); for
d < e this is SixCells.cell_criterion: cell (a + s u) mod 6 in {1,...,4}, a = ((d i + q) mod 6E) / E, d = 6q + s.
Per flank: coarse row i = 0 (FreeFlank's shifts: (6 u E + 1)/(6e)); whether all six coarse shifts are blocked;
then the finer rows i = 1..E-1: which (i, u) are lonely (free cells). Per row i, the number of shifts u blocked by
each runner (the budget: 6 shifts). Summary over sets: does some divisible flank have a free cell; the least such
i; blocked-shift counts per runner by its residue class s = d mod 6.
Usage: six_cells_budget_v1.py"""
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
def clear(d, e, j): r = d * (6 * j + 1) % (6 * e); return e <= r <= 5 * e
nsets = 0; flanks = 0; coarse_all_blocked = 0; free_after = Counter(); least_i = Counter(); set_has_free = Counter()
per_runner = Counter(); row_total = Counter(); free_cells = Counter(); exceptions = []
for r in rows:
    S = eval(r[0]); nsets += 1; any_free = False
    for e in [d for d in S if d % 6 == 0]:
        E = e // 6; flanks += 1
        coarse_free = [u for u in range(6) if all(clear(d, e, u * E) for d in S)]
        if coarse_free: free_after["coarse shift free"] += 1; any_free = True; continue
        coarse_all_blocked += 1
        frees = [(i, u) for i in range(1, E) for u in range(6) if all(clear(d, e, u * E + i) for d in S)]
        free_after["all coarse blocked; some finer cell free" if frees else "all coarse blocked; no cell free"] += 1
        free_cells[min(len(frees), 10)] += 1
        if frees:
            any_free = True; i0 = frees[0][0]; least_i[(i0, E) if E <= 6 else ("i/E", round(i0 / E, 1))] += 1
        # budget per row: shifts u blocked by each runner, by residue class s = d mod 6 (s = 0: other multiples)
        for i in range(E):
            tot = 0
            for d in S:
                if d == e: continue
                b = sum(1 for u in range(6) if not clear(d, e, u * E + i))
                per_runner[(d % 6, b)] += 1; tot += b
            row_total[min(tot, 12)] += 1
    set_has_free["some divisible flank has a lonely opening" if any_free else "no divisible flank has one"] += 1
    if not any_free and len(exceptions) < 10: exceptions.append(S)
print(f"residual sets {nsets}; divisible flanks {flanks}")
print("flanks:", dict(free_after))
print("free finer cells per all-coarse-blocked flank (10 = 10+):", dict(sorted(free_cells.items())))
print("least row i with a free cell (exact for E <= 6, else as i/E):", dict(least_i.most_common(14)))
print("sets:", dict(set_has_free))
print("sets with no divisible flank lonely, examples:", exceptions)
print("shifts blocked per runner per row, by (d mod 6, count):", dict(sorted(per_runner.items())))
print("total blocked shifts per row (with overlaps; 6 needed to block every shift):", dict(sorted(row_total.items())))
