#!/usr/bin/env python3
"""E43: residue alignment of blocked shifts at divisible flanks (SixResidual, [1,40]). Flank e = 6E, row i < E,
shifts u < 6, opening j = uE + i. Runner d: s = d mod 6, phase a = sixth of its reading at opening i
(a = floor(6 * (d(6i+1) mod 6e) / 6e)); for d < e this is cell_criterion's a = ((d i + q) mod 6E)/E. Shape rule:
d blocks u iff (a + s u) mod 6 in {0, 5}. Shapes: s in {1, 5}: an adjacent pair of shifts; s in {2, 4}: an
antipodal pair {c, c+3}; s = 3: a parity class (3 shifts) or none; s = 0: all six or none.
Control: the shape rule against direct blocking, every runner, row, shift (for s = 0 the exact reading decides,
since a reading exactly at 5/6 is clear; cell_criterion covers s = 1..5 only).
Then, per row: the union of blocked shifts; rows are FREE (union != Z/6) or FULL. In rows where the blocked counts sum
to >= 6, record which runner pairs share a blocked shift (by shape classes) and the phase relation that makes them
coincide, for FREE and FULL rows separately."""
from collections import Counter
from itertools import combinations
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
def clear(d, e, j): r = d * (6 * j + 1) % (6 * e); return e <= r <= 5 * e
def shape(s): return {1: "unit", 5: "unit", 2: "even", 4: "even", 3: "three", 0: "mult"}[s]
ctrl = Counter(); unions = {"FREE": Counter(), "FULL": Counter()}; pairs = {"FREE": Counter(), "FULL": Counter()}
overlap_rows = Counter(); shapes_free = Counter(); shapes_full = Counter(); rel = {"FREE": Counter(), "FULL": Counter()}
for r in rows:
    S = eval(r[0])
    for e in [d for d in S if d % 6 == 0]:
        E = e // 6
        for i in range(E):
            blk = {}
            for d in S:
                if d == e: continue
                s = d % 6; a = 6 * (d * (6 * i + 1) % (6 * e)) // (6 * e)
                direct = frozenset(u for u in range(6) if not clear(d, e, u * E + i))
                if s == 0:   # another multiple of 6: its reading does not move with u; exact edge 5/6 is clear
                    rr = d * (6 * i + 1) % (6 * e); rule = frozenset(range(6)) if not (e <= rr <= 5 * e) else frozenset()
                else:
                    rule = frozenset(u for u in range(6) if (a + s * u) % 6 in (0, 5))
                ctrl[direct == rule] += 1
                blk[d] = (s, a, direct)
            union = frozenset().union(*[b[2] for b in blk.values()])
            kind = "FREE" if len(union) < 6 else "FULL"
            tot = sum(len(b[2]) for b in blk.values())
            unions[kind][len(union)] += 1
            if tot < 6: continue
            overlap_rows[kind] += 1
            sig = tuple(sorted(shape(b[0]) + ("" if b[2] else "(0)") for b in blk.values()))
            (shapes_free if kind == "FREE" else shapes_full)[sig] += 1
            for (d1, b1), (d2, b2) in combinations(blk.items(), 2):
                if b1[2] and b2[2] and (b1[2] & b2[2]):
                    k = tuple(sorted((shape(b1[0]), shape(b2[0]))))
                    pairs[kind][k] += 1
                    if shape(b1[0]) == shape(b2[0]) == "unit":
                        # adjacent pairs {c, c+1}: c = (5 - a) mod 6 for s = 1 (u with a + u = 5), c = a mod 6 for s = 5
                        c1 = (5 - b1[1]) % 6 if b1[0] == 1 else b1[1] % 6
                        c2 = (5 - b2[1]) % 6 if b2[0] == 1 else b2[1] % 6
                        rel[kind][("unit-unit", "same pair" if c1 == c2 else "shifted by one")] += 1
print("control (shape rule == direct blocking):", dict(ctrl))
for k in ("FREE", "FULL"):
    print(f"{k} rows: |union of blocked shifts|:", dict(sorted(unions[k].items())))
print("rows with blocked counts summing to >= 6:", dict(overlap_rows))
print("FREE rows, runner shapes (0) = blocks nothing:", shapes_free.most_common(8))
print("FULL rows, runner shapes:", shapes_full.most_common(8))
for k in ("FREE", "FULL"):
    tot = overlap_rows[k]
    print(f"{k} rows: overlapping pairs by shape (per row):", {p: round(c / tot, 2) for p, c in pairs[k].most_common(8)})
    print(f"{k} rows: unit-unit overlaps:", dict(rel[k]))
