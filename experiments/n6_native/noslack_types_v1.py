#!/usr/bin/env python3
"""Observation only. The 2,989 SixResidual sets (E75) whose other-four window at the cascade instant has no 1/5 instant,
cross-tabulated with the cascade outcome types recorded earlier in this log: BHK case label (tsv), number of moves,
final flank rank and its opening (lap) k, setter-rank path, early/late (v1 T < 1/3, E6), final-flank-fastest."""
from fractions import Fraction as F
from collections import Counter
import importlib.util
sp = importlib.util.spec_from_file_location("cw", "cascade_vs_window_v1.py")
src = open("cascade_vs_window_v1.py").read().split('print("(1) family')[0]
exec(src)
rows = [l.rstrip("\n").split("\t") for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
tab = {k: [Counter(), Counter()] for k in ("bhk", "moves", "final (rank,k)", "path", "early", "flank fastest")}
n = [0, 0]
for r in rows:
    S = eval(r[0]); T, b = cascade(S); R = tuple(d for d in S if d != b); Lw, Uw = window(R, T)
    g = 0 if slack_in(R, Lw, Uw) else 1; n[g] += 1
    ranks = eval(r[3]); laps = eval(r[4])
    k = laps[-1] if laps else 0
    tab["bhk"][g][r[1]] += 1; tab["moves"][g][min(int(r[2]), 4)] += 1
    tab["final (rank,k)"][g][(S.index(b) + 1, k)] += 1; tab["path"][g][ranks] += 1
    tab["early"][g][S[0] * T < F(1, 3)] += 1; tab["flank fastest"][g][b == S[-1]] += 1
print(f"with order-five slack: {n[0]}; without: {n[1]}")
for key, (a, b) in tab.items():
    print(f"== {key}")
    print("   without slack:", [(k, c, round(c / n[1], 3)) for k, c in b.most_common(8)])
    print("   with slack:   ", [(k, c, round(c / n[0], 3)) for k, c in a.most_common(8)])
