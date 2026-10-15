#!/usr/bin/env python3
"""E37: the phase condition in short J123 windows (l4 < 1/2), §5. Work in runner-4 laps from the window start:
runner 4 reads a4 + u, runner 5 reads a5 + rho u (rho = d5/d4), u in [0, l4]. A shared clear point of positive
length is the box criterion for two runners in a window: some clear piece of 4 and some clear piece of 5 overlap
inside [0, l4]. With l4 < 1/2 runner 4 has at most one entry or exit in the window. Cases by the start readings
(B = in the open band (1/6, 5/6) mod 1, X = otherwise):
  BB: success at once.
  BX: 5 must enter (wait w5 = ((1/6 - a5) mod 1)/rho) before 4 exits (5/6 - a4) and before the window ends (l4).
  XB: 4 must enter (w4 = (1/6 - a4) mod 1) before the window ends, and 5 must be clear somewhere in
      [w4, l4] (it is clear at w4, or it enters before l4 having been blocked at w4).
  XX: both must enter, and their clear pieces overlap before l4.
The race outcome is computed exactly from the pieces; the script checks its case logic against the window file's
own `shared` flag, then records, for each failure, which event came first: runner 4's exit, runner 5's exit,
runner 3's exit (the window end), or a missed entry. Residues: a4 and a5 are frac(d J0), J0 = entry of runner 1 or
2 at its opening k, so a = (d (6k+1) mod 6 d_j) / (6 d_j).
Usage: six_s5_race_v1.py"""
import ast
from fractions import Fraction as F
from collections import Counter
s6, s56 = F(1, 6), F(5, 6)
def frac(z): return z - (z.numerator // z.denominator)
def inB(a): return s6 < a < s56
rows = [l.rstrip("\n").split("\t") for l in open("six_s5_window45_v1.tsv")][1:]
mism = 0; cases = Counter(); why = Counter(); succ_tight = Counter(); n = 0
for r in rows:
    S = ast.literal_eval(r[0]); a4, a5 = F(r[4]), F(r[5]); l4 = F(r[6]); shared = r[8] == "True"
    if l4 >= F(1, 2): continue
    n += 1; rho = F(S[4], S[3])
    e4 = F(0) if inB(a4) else (s6 - a4) % 1               # 4's entry (0 if already clear)
    x4 = (s56 - a4) % 1 if inB(a4) else e4 + F(2, 3)      # 4's exit (laps of 4)
    e5 = F(0) if inB(a5) else ((s6 - a5) % 1) / rho
    x5 = ((s56 - a5) % 1) / rho if inB(a5) else e5 + F(2, 3) / rho
    # runner 5 may leave and re-enter within the window: list its pieces up to l4
    p5 = []; e, x = e5, x5
    while e < l4:
        p5.append((e, min(x, l4))); e, x = x + F(1, 3) / rho, x + F(1, 3) / rho + F(2, 3) / rho
    p4 = []; e, x = e4, x4
    while e < l4:
        p4.append((e, min(x, l4))); e, x = x + F(1, 3), x + F(1, 3) + F(2, 3)
    ok = any(max(a, c) < min(b, d) for a, b in p4 for c, d in p5)
    mism += ok != shared
    key = ("B" if inB(a4) else "X") + ("B" if inB(a5) else "X"); cases[(key, "success" if shared else "failure")] += 1
    if not shared:
        if e4 >= l4: why[(key, "4 enters after the window ends (runner 3's exit)")] += 1
        elif not p5: why[(key, "5 enters after the window ends")] += 1
        elif len(p4) == 1 and min(c for c, d in p5) >= min(x4, l4): why[(key, "5 enters after 4 leaves" if x4 < l4 else "5 enters after the window ends")] += 1
        elif len(p4) > 1: why[(key, "4 leaves and re-enters; 5's pieces miss both")] += 1
        else: why[(key, "5 clear only while 4 blocked, or leaves before 4 enters")] += 1
    else:
        # the binding race in successes: which constraint has the smallest slack
        if key == "BX":
            sl = {"5's entry vs 4's exit": x4 - e5, "5's entry vs window end": l4 - e5}
            succ_tight[(key, min(sl, key=sl.get))] += 1
        elif key == "XB":
            succ_tight[(key, "5 still clear at 4's entry" if any(c <= e4 < d for c, d in p5) else "5 enters after 4")] += 1
print(f"short windows (l4 < 1/2): {n}; case logic against the shared flag: mismatches {mism}")
print("cases:", dict(sorted(cases.items())))
print("failures, first event:", dict(why.most_common()))
print("successes, binding race:", dict(succ_tight.most_common()))
