#!/usr/bin/env python3
"""Classify the exceptions of seven_cells_v1 (EXACT): sets with a multiple of 7 but no lonely opening at any 7-divisible
flank.  Per exception: the rank of the 7-multiple(s); the number of runners faster than it; and the cascade's lonely
instant T read as a flank opening (7j+1)/(7d) or (7j+6)/(7d) of some runner d, with d's residue mod 7 and the readings
of all runners at T multiplied by 7 (residues of 7 d' T)."""
import ast, math, sys
from fractions import Fraction as F
from collections import Counter
sys.path.insert(0, ".")
from seven_cascade_observe_v1 import cascade
exc = [ast.literal_eval(l) for l in open(sys.argv[1]) if l.strip()]
pos = Counter(); faster = Counter(); fl = Counter(); edge = Counter(); ex = []
for S in exc:
    M = [i for i, d in enumerate(S) if d % 7 == 0]
    pos[tuple(i + 1 for i in M)] += 1
    faster[5 - M[-1]] += 1
    T, mv = cascade(S)
    # which runners sit exactly on an edge at T
    ed = [(i + 1, "in" if (d * T - (d * T).numerator // (d * T).denominator) == F(1, 7) else "out")
          for i, d in enumerate(S) if (d * T - (d * T).numerator // (d * T).denominator) in (F(1, 7), F(6, 7))]
    fl[(tuple(e for e, _ in ed), T.denominator % 7 == 0)] += 1
    if len(ex) < 12: ex.append((S, str(T), ed))
print(f"{len(exc)} exceptions")
print("  rank(s) of the 7-multiple(s):", sorted(pos.items()))
print("  runners faster than the (largest) 7-multiple:", sorted(faster.items()))
print("  runners on an edge at the cascade's instant, and whether 7 | denominator(T):", fl.most_common(15))
print("  examples (set, T, edge runners):", ex)
