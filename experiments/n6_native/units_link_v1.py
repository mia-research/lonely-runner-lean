#!/usr/bin/env python3
"""E45: does the unit/blocking structure connect to the tight (degenerate) sets and to SixResidual?
(a) tight sets of tight_general_v1.out: residues mod n; contain every unit? contain a minimal coarse-blocking pattern?
(b) SixResidual ([1,40]): residues of the non-multiples of 6: contain both units {1,5}? contain a minimal blocking
    pattern {1,2,3,5} or {1,3,4,5}? Against all primitive 5-sets in [1,40] with a multiple of 6 (control base rate).
(c) the 34 sets of E42 with neither a divisible-flank opening nor a lap-point shift."""
import re, math
from itertools import combinations
from collections import Counter
units = {3: {1,2}, 4: {1,3}, 5: {1,2,3,4}, 6: {1,5}, 7: {1,2,3,4,5,6}, 8: {1,3,5,7}}
pats = {6: [{1,2,3,5}, {1,3,4,5}], 8: [{1,3,4,5,7}]}
print("(a) tight sets:")
for line in open("tight_general_v1.out"):
    if line.startswith("TIGHT"):
        S = [int(x) for x in line.split(":")[0].split()[1:]]; n = len(S) + 1
        R = {d % n for d in S}
        print(f"   n={n} {S}: residues {sorted(R)}; all units {units[n] <= R}; contains a blocking pattern {any(p <= R for p in pats.get(n, []))}")
def classify(S):
    R = {d % 6 for d in S if d % 6}
    return ("units {1,5} " + ("yes" if {1, 5} <= R else "no"), "pattern " + ("yes" if any(p <= R for p in pats[6]) else "no"))
res = Counter(classify(eval(l.split("\t")[0])) for l in list(open("six_cascade_observe_v1.tsv"))[1:])
print("(b) SixResidual [1,40]:", dict(res))
base = Counter()
for S in combinations(range(1, 41), 5):
    if math.gcd(*S) != 1 or not any(d % 6 == 0 for d in S): continue
    base[classify(S)] += 1
print("    control: all primitive 5-sets in [1,40] with a multiple of 6:", dict(base))
left = [(1,2,6,8,10),(1,3,4,5,6),(1,3,4,5,12),(1,3,5,8,12),(1,4,5,9,12),(1,4,5,9,18),(1,4,12,16,20),(1,5,8,9,12)]
print("(c) E42 leftover examples:", [(S, sorted({d % 6 for d in S if d % 6})) for S in left])
