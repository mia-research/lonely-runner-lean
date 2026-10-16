#!/usr/bin/env python3
"""Order seven exception mechanism, primitive <= H.
 T5: which runner is folded (index r of v1..v6) and how many 5-blocks close the set.
 T6 / TIGHT: the longest lonely interval [L, U]; the runners whose band edges fix L and U (index, edge 1/7 or 6/7,
 lap m), L and U as exact fractions (edge instants (m + e/7)/v), and the runner-1 lap position v1 L."""
import math, sys
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("o7_map_v1.py").read().split("def run(")[0])
H = int(sys.argv[1]) if len(sys.argv) > 1 else 30
def edge(S, x):
    """runners k with an edge (m + e/7)/v_k equal to x (e in {1, 6})."""
    out = []
    for k, v in enumerate(S):
        for e in (1, 6):
            m = round(x * v - e / 7)
            if abs((m + e / 7) / v - x) < 1e-10: out.append((k + 1, e, m, F(7 * m + e, 7 * v)))
    return out
fold = Counter(); nblk = Counter(); t6 = []
for S in combinations(range(1, H + 1), 6):
    if math.gcd(*S) != 1: continue
    k, p = classify(S)
    if k == "T5":
        fold[p[0]] += 1
        n = sum(1 for idx in combinations(range(6), 5)
                for r in [[q for q in range(6) if q not in idx][0]]
                if any(S[r] * (U - L) >= 2 / 7 - EPS for L, U in block(S, idx)))
        nblk[n] += 1
    elif k in ("T6", "TIGHT"):
        iv = block(S, range(6), strict=(k == "T6"))
        L, U = max(iv, key=lambda z: z[1] - z[0])
        t6.append((k, S, edge(S, L), edge(S, U)))
print(f"primitive <= {H}")
print("  T5 folded runner index:", sorted(fold.items()))
print("  T5 number of closing 5-blocks:", sorted(nblk.items()))
lowE = Counter(); upE = Counter()
for k, S, eL, eU in t6:
    lowE[tuple(sorted((a, e) for a, e, _, _ in eL))] += 1; upE[tuple(sorted((a, e) for a, e, _, _ in eU))] += 1
    L = eL[0][3]; U = eU[0][3]
    print(f"  {k} {S}: L = {L} U = {U} length {U - L}  v1 L = {S[0] * L}  L-edges {[(a, e) for a, e, _, _ in eL]}"
          f"  U-edges {[(a, e) for a, e, _, _ in eU]}")
print("  lower-edge patterns:", lowE.most_common()); print("  upper-edge patterns:", upE.most_common())
