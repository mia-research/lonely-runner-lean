#!/usr/bin/env python3
"""E36 reader: ending window index; lengths of ending vs failing windows (in runner-4 laps); largest failing l4 by
the speed ratio d5/d4; for failing windows of each kind, the readings a4, a5 at the window start."""
import ast
from fractions import Fraction as F
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open("six_s5_window45_v1.tsv")][1:]
endidx = Counter(); Lend = Counter(); Lfail = Counter(); maxf = {}; kinds = {}
for r in rows:
    S = ast.literal_eval(r[0]); l4 = F(r[6]); shared = r[8] == "True"; cT = r[10] == "True"
    if shared and cT: endidx[int(r[1])] += 1; Lend[min(round(float(l4), 1), 1.0)] += 1
    if not shared:
        Lfail[min(round(float(l4), 1), 1.0)] += 1
        q = S[4] / S[3]; b = "d5/d4 < 1.5" if q < 1.5 else ("1.5-2" if q < 2 else ("2-3" if q < 3 else "3+"))
        if l4 > maxf.get(b, (F(0),))[0]: maxf[b] = (l4, S)
        a4, a5 = F(r[4]), F(r[5])
        def where(a): return "blocked" if (a < F(1, 6) or a > F(5, 6)) else ("clear")
        kinds.setdefault(r[9], Counter())[(where(a4), where(a5))] += 1
print("ending window index (0 = first J123 window):", dict(sorted(endidx.items())))
print("ending windows, length in 4-laps (1.0 = 1+):", dict(sorted(Lend.items())))
print("failing windows, length in 4-laps:", dict(sorted(Lfail.items())))
print("largest failing l4 by d5/d4:", {k: (float(v[0]), v[1]) for k, v in sorted(maxf.items())})
for k, c in kinds.items(): print(f"failing '{k}': (runner 4, runner 5) at the window start:", dict(c))
