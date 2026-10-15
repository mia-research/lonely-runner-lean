#!/usr/bin/env python3
"""E29: readings of every runner at the takeover instant tB, at each death of the isolation box (six_handover_v1.tsv).
Speeds at the death: runners faster-indexed than the mover at their targets S, slower-indexed at the grid v1*i, the
mover at x. Roles: M (mover), F (A's flank, entering at the death), s (slower than M, not F), f (faster than M, not F).
Per runner: reading at the death instant tA (in band), advance (tB - tA)*d_i in laps, reading at tB, slack at tB
(distance to the nearer edge of [1/6, 5/6]) and which edge. B's two binding runners: its flank (latest entry, reads
1/6) and its closer (earliest exit, smallest 5/6-side slack). Kind 1 = B's flank is M (tB = M's next entry);
kind 2 = otherwise. Usage: six_takeover_readings_v1.py file.tsv"""
import sys, ast
from fractions import Fraction as F
from collections import Counter
s6, s56 = F(1, 6), F(5, 6)
def frac(z): return z - (z.numerator // z.denominator)
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
stats = {}
for r in rows:
    if r[8] == "NONE": continue
    grp = r[0]; S = ast.literal_eval(r[1]); m = int(r[2]); x = F(r[3])
    fA = ast.literal_eval(r[5]); fB = ast.literal_eval(r[9]); tA, tB = F(r[6]), F(r[10])
    W = [F(S[i]) if i + 1 > m else F(S[0] * (i + 1)) for i in range(5)]; W[m - 1] = x
    kind = "kind1 (M's next entry)" if m in fB else "kind2 (later)"
    def role(i):
        if i == m: return "M"
        if i in fA: return "F"
        return "s" if i < m else "f"
    st = stats.setdefault((grp, kind), {"n": 0, "closer": Counter(), "flank": Counter(), "near_entry": Counter(),
                                        "near_exit": Counter(), "advF": Counter(), "rdF": Counter(), "rdM": Counter(),
                                        "minslack": Counter(), "pair": Counter()})
    st["n"] += 1
    rdB = [frac(W[i - 1] * tB) for i in range(1, 6)]
    slack = {i: min(rdB[i-1] - s6, s56 - rdB[i-1]) for i in range(1, 6)}
    exit_side = {i: s56 - rdB[i-1] for i in range(1, 6)}
    closer = min(range(1, 6), key=lambda i: exit_side[i])
    st["closer"][role(closer)] += 1
    st["flank"]["+".join(sorted(role(i) for i in fB))] += 1
    st["pair"][(role(fB[0]), role(closer))] += 1
    # which runners sit within 1/12 of an edge at tB (other than B's flank, which reads 1/6 exactly)
    for i in range(1, 6):
        if i in fB: continue
        if rdB[i-1] - s6 < F(1, 12): st["near_entry"][role(i)] += 1
        if s56 - rdB[i-1] < F(1, 12): st["near_exit"][role(i)] += 1
    for i in fA:
        if i != m:
            st["rdF"][str(rdB[i-1]) if rdB[i-1].denominator <= 12 else round(float(rdB[i-1]), 2)] += 1
            st["advF"][round(float((tB - tA) * W[i-1]), 2)] += 1
    st["rdM"][str(rdB[m-1]) if rdB[m-1].denominator <= 12 else round(float(rdB[m-1]), 2)] += 1
    st["minslack"][role(min((i for i in range(1, 6) if i not in fB), key=lambda i: slack[i]))] += 1
for (grp, kind), st in sorted(stats.items()):
    print(f"== {grp}, {kind}: {st['n']} deaths")
    print("   B's flank role(s):", dict(st["flank"].most_common()))
    print("   B's closer (earliest exit) role:", dict(st["closer"].most_common()))
    print("   (flank, closer) roles:", dict(st["pair"].most_common(8)))
    print("   runner with least slack, B's flank excluded:", dict(st["minslack"].most_common()))
    print("   within 1/12 of entry edge:", dict(st["near_entry"]), "; within 1/12 of exit edge:", dict(st["near_exit"]))
    print("   A's flank F: reading at tB", dict(st["rdF"].most_common(6)), "; advance tA->tB in laps", dict(st["advF"].most_common(6)))
    print("   mover M: reading at tB", dict(st["rdM"].most_common(6)))
