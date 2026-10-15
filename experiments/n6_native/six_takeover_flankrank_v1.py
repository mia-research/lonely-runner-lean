#!/usr/bin/env python3
"""E29: identity of A's flank F relative to the mover M, by kind; and in kind 2, whether B's instant is F's next
entry (advance exactly one F-lap) or a faster runner's entry. Also d_F/x (F's speed over the mover's)."""
import sys, ast
from fractions import Fraction as F
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
for grp in ("ordinary", "chain"):
    c = Counter(); ratio = Counter(); k2 = Counter()
    for r in rows:
        if r[0] != grp or r[8] == "NONE": continue
        S = ast.literal_eval(r[1]); m = int(r[2]); x = F(r[3]); fA = ast.literal_eval(r[5]); fB = ast.literal_eval(r[9])
        W = [F(S[i]) if i + 1 > m else F(S[0] * (i + 1)) for i in range(5)]; W[m - 1] = x
        tA, tB = F(r[6]), F(r[10]); f = fA[0]
        kind = "kind1" if m in fB else "kind2"
        c[(kind, "F = runner %d" % f, "F slower than M" if W[f-1] < x else "F faster than M")] += 1
        if kind == "kind1": ratio[round(float(W[f-1] / x), 1)] += 1
        else:
            adv = (tB - tA) * W[f-1]
            if f in fB: k2[f"B at F's entry, F laps later = {adv}"] += 1
            else: k2["B at another runner's entry (%s)" % ("faster than M" if W[fB[0]-1] > x else "slower than M")] += 1
    print(f"== {grp}")
    for k, v in sorted(c.items()): print("  ", k, v)
    print("   kind1 d_F/x:", dict(sorted(ratio.items())))
    print("   kind2:", dict(k2.most_common(8)))
