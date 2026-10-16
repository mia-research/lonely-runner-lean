#!/usr/bin/env python3
"""Order seven exceptions (T5, T6 of o7_map_v1), primitive <= H, by structural feature (first that applies):
  slow:    v5 <= 6 v1   (bounded slow block, the analogue of order six's v3 <= 3 v1)
  cluster: v5 - v2 <= v1 (runners 2..5 within one v1 of each other)
  half:    v4 <= 3 v1   (bounded 4-prefix)
  other.
Shares among exceptions and among all sets. Exact check (fractions) that every T6 set has a positive-length lonely
interval, and that the only TIGHT set is lonely at a single point."""
import math, sys
from itertools import combinations
from collections import Counter
from fractions import Fraction as Fr
exec(open("o7_map_v1.py").read().split("def run(")[0])
def feat(S):
    v1, v2, v3, v4, v5, v6 = S
    if v5 <= 6 * v1: return "slow"
    if v5 - v2 <= v1: return "cluster"
    if v4 <= 3 * v1: return "half"
    return "other"
def exact_max_len(S):
    cur = [(Fr(6 * m + 1, 7 * 6 * 0 + 7 * S[0]) , None) for m in []]
    def bands_f(v): return [(Fr(7 * m + 1, 7 * v), Fr(7 * m + 6, 7 * v)) for m in range(v)]
    cur = bands_f(S[0])
    for v in S[1:]:
        B = bands_f(v); i = j = 0; out = []
        while i < len(cur) and j < len(B):
            lo, hi = max(cur[i][0], B[j][0]), min(cur[i][1], B[j][1])
            if hi >= lo: out.append((lo, hi))
            if cur[i][1] < B[j][1]: i += 1
            else: j += 1
        cur = out
    return max((hi - lo for lo, hi in cur), default=None)
H = int(sys.argv[1]) if len(sys.argv) > 1 else 30
allf = Counter(); exf = Counter(); t6 = []; tight = []
for S in combinations(range(1, H + 1), 6):
    if math.gcd(*S) != 1: continue
    f = feat(S); allf[f] += 1
    k, p = classify(S)
    if k in ("T5", "T6"): exf[(k, f)] += 1
    if k == "T6": t6.append((S, f))
    if k == "TIGHT": tight.append(S)
print(f"primitive <= {H}: all sets by feature {dict(allf)}")
print("exceptions by (kind, feature):", dict(sorted(exf.items())))
print("T6 sets with feature and exact max lonely length:")
for S, f in t6: print("   ", S, f, exact_max_len(S))
print("TIGHT sets, exact max lonely length (0 = isolated instants):", [(S, exact_max_len(S)) for S in tight])
