#!/usr/bin/env python3
"""E43: the rows of E42/E43 in CRT coordinates, shift u <-> (u mod 2, u mod 3). Runner shapes (control in
six_cells_align_v1.out): d = 3 mod 6 removes a parity layer; d = 2, 4 mod 6 removes a mod-3 column; d = 1, 5 mod 6
removes one point in each parity layer; another multiple of 6 removes everything or nothing. For each parity layer
p not removed: R = columns removed by even runners, P = points removed by unit runners in that layer;
free points in layer p = 3 - |R| - |P \\ R|. Rows (skipping rows where another multiple of 6 blocks everything):
decomposed by (|R|, |P|, |P cap R|, number of unit runners) in the best layer, FREE vs FULL. The 'alignment' is
P cap R (a unit runner's point inside an even runner's column) and coinciding unit points."""
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
def clear(d, e, j): r = d * (6 * j + 1) % (6 * e); return e <= r <= 5 * e
dec = {"FREE": Counter(), "FULL": Counter()}; mismatch = 0; skipped = 0; nlay = {"FREE": Counter(), "FULL": Counter()}
for r in rows:
    S = eval(r[0])
    for e in [d for d in S if d % 6 == 0]:
        E = e // 6
        for i in range(E):
            blocked = {d: {u for u in range(6) if not clear(d, e, u * E + i)} for d in S if d != e}
            if any(d % 6 == 0 and len(b) == 6 for d, b in blocked.items()): skipped += 1; continue
            layers_removed = {u % 2 for d, b in blocked.items() if d % 6 == 3 and b for u in b}
            R = {u % 3 for d, b in blocked.items() if d % 6 in (2, 4) for u in b}
            units = [b for d, b in blocked.items() if d % 6 in (1, 5)]
            best = None
            for p in (0, 1):
                if p in layers_removed: continue
                P = {u % 3 for b in units for u in b if u % 2 == p}
                nP = sum(1 for b in units for u in b if u % 2 == p)      # with multiplicity
                free = 3 - len(R) - len(P - R)
                cand = (free, len(R), len(P), len(P & R), nP)
                if best is None or cand > best: best = cand
            union = set().union(*blocked.values())
            kind = "FREE" if len(union) < 6 else "FULL"
            nlay[kind][2 - len(layers_removed)] += 1
            pred_free = best is not None and best[0] > 0
            mismatch += pred_free != (kind == "FREE")
            if best is not None:
                f, nR, nP_, nPR, mult = best
                dec[kind][(f"|R|={nR}", f"units' points={mult}", f"distinct={nP_}", f"inside R={nPR}")] += 1
            else:
                dec[kind][("both layers removed",)] += 1
print("rows skipped (another multiple of 6 blocks every shift):", skipped)
print("CRT layer rule vs union: mismatches", mismatch)
for k in ("FREE", "FULL"):
    print(f"{k}: parity layers left open by d = 3 mod 6 runners:", dict(nlay[k]))
    for key, c in dec[k].most_common(10): print(f"   {k} {c:6d}  {key}")
