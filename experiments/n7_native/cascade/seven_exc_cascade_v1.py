#!/usr/bin/env python3
"""Exceptions of seven_cells_v1 through the cascade (EXACT, observation only).  For each exception: moves, setter ranks
with laps, final flank rank, and the rank of the multiple of 7 (m).  Also, at the final instant T, the lap counts
floor(d T) of every runner and whether m has completed at least one lap (m T >= 1)."""
import ast, sys
from fractions import Fraction as F
from collections import Counter
from seven_cascade_observe_v1 import cascade
exc = [ast.literal_eval(l) for l in open(sys.argv[1]) if l.strip()]
nm = Counter(); seqs = Counter(); fin = Counter(); mlap = Counter(); first = Counter(); ex = []
for S in exc:
    T, mv = cascade(S)
    ranks = tuple(r for r, _ in mv); fr = ranks[-1] if ranks else 1
    mi = [i + 1 for i, d in enumerate(S) if d % 7 == 0][0]
    nm[len(mv)] += 1; seqs[(mi, ranks)] += 1; fin[(mi, fr)] += 1
    first[(mi, ranks[0] if ranks else None)] += 1
    laps = tuple((d * T).numerator // (d * T).denominator for d in S)
    mlap[(mi, laps[mi - 1])] += 1
    if len(ex) < 10: ex.append((S, mv, str(T), laps))
print(f"{len(exc)} exceptions")
print("  moves:", sorted(nm.items()))
print("  (rank of m, first setter rank):", sorted(first.items(), key=str))
print("  (rank of m, final flank rank):", sorted(fin.items()))
print("  (rank of m, laps of m at T):", sorted(mlap.items())[:20])
print("  commonest (rank of m, setter sequence):", seqs.most_common(12))
print("  examples (set, moves (rank, lap), T, laps):", ex)
