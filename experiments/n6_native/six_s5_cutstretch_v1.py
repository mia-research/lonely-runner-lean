#!/usr/bin/env python3
"""E35: §5 cascade endings in the cut-stretch language (E31-E34). §5 = BHK case D | v1 (column bhk_case = S5 in
six_cascade_observe_v1.tsv); runners 1-3 merge (v1 + v2 = v3 reduction, E15/E17). At the cascade's ending instant T:
  J123 = the stretch around T on which runners 1, 2, 3 are all clear (intersection of their current bands);
  the cutters are runners 4 and 5; inside J123 the lonely pieces are where 4 and 5 are both clear.
Records: |J123| in laps of runner 4 and of runner 5; how many bands of 4 and of 5 meet J123; the number of lonely
pieces in J123 and which one (in time order) contains T; who sets J123's ends (runner index); who sets the ending
piece's ends; and whether T is the start of its piece (the cascade lands at a piece's left end).
Usage: six_s5_cutstretch_v1.py"""
import math
from fractions import Fraction as F
from collections import Counter
s6, s56 = F(1, 6), F(5, 6)
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
def bands_in(d, a, b):
    """clear bands of speed d meeting (a, b) in positive length, as clipped intervals"""
    out = []; k = math.floor(a * d - s56)
    while (6*k+1) / (6*d) < b:
        lo, hi = max(a, (6*k+1)/(6*d)), min(b, (6*k+5)/(6*d))
        if lo < hi: out.append((lo, hi))
        k += 1
    return out
J4 = Counter(); J5 = Counter(); nb4 = Counter(); nb5 = Counter(); npieces = Counter(); which = Counter()
jends = Counter(); pends = Counter(); start = Counter(); n = 0; first_ok = Counter()
for r in rows:
    if r[1] != "S5": continue
    S = [F(x) for x in eval(r[0])]; T = F(r[5]); n += 1
    k = [math.floor(d * T) for d in S]
    ent = [(6*k[i]+1) / (6*S[i]) for i in range(5)]; ext = [(6*k[i]+5) / (6*S[i]) for i in range(5)]
    J0 = max(ent[:3]); J1 = min(ext[:3])
    jl = [i + 1 for i in range(3) if ent[i] == J0][0]; jr = [i + 1 for i in range(3) if ext[i] == J1][0]
    jends[(jl, jr)] += 1
    J4[min(round(float((J1 - J0) * S[3]), 1), 3.0)] += 1; J5[min(round(float((J1 - J0) * S[4]), 1), 3.0)] += 1
    b4 = bands_in(S[3], J0, J1); b5 = bands_in(S[4], J0, J1); nb4[min(len(b4), 6)] += 1; nb5[min(len(b5), 6)] += 1
    pieces = sorted((max(a1, a2), min(c1, c2)) for a1, c1 in b4 for a2, c2 in b5 if max(a1, a2) < min(c1, c2))
    npieces[min(len(pieces), 6)] += 1
    idx = [i for i, (a, b) in enumerate(pieces) if a <= T <= b]
    which[idx[0] + 1 if idx else "T in no positive piece"] += 1
    if idx:
        a, b = pieces[idx[0]]
        left = [i + 1 for i in range(5) if ent[i] == a] if any(ent[i] == a for i in range(5)) else ["?"]
        right = [i + 1 for i in range(5) if ext[i] == b] if any(ext[i] == b for i in range(5)) else ["?"]
        pends[(tuple(left), tuple(right))] += 1
        start["T is the piece's left end" if T == a else "T inside the piece"] += 1
print(f"§5 endings: {n}")
print("  J123 ends set by (left, right) runner:", dict(jends.most_common()))
print("  |J123| in laps of runner 4 (3.0 = 3+):", dict(sorted(J4.items())))
print("  |J123| in laps of runner 5 (3.0 = 3+):", dict(sorted(J5.items())))
print("  bands of 4 meeting J123:", dict(sorted(nb4.items())), "; bands of 5:", dict(sorted(nb5.items())))
print("  lonely pieces in J123 (6 = 6+):", dict(sorted(npieces.items())))
print("  piece containing T (1 = first in time):", dict(which.most_common()))
print("  ending piece ends set by (left, right) runners:", dict(pends.most_common(10)))
print("  ", dict(start))
