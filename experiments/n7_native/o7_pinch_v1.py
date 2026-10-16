#!/usr/bin/env python3
"""Phase 2: exact pinch data for the 41 T6 sets (o7_map_v2_60.out). All lonely intervals over [0, 1) exactly
(fractions); for the longest: entering edge (runner i, lap m) with L = (7m+1)/(7 v_i), leaving edge (runner j,
lap m') with U = (7m'+6)/(7 v_j); for each other runner k its lap n_k and slack (distance of v_k [L, U] from the
band edges, in lap units)."""
import re
from fractions import Fraction as Fr
T6 = [tuple(map(int, m.group(1).split(","))) for m in re.finditer(r"T6 \(([0-9, ]+)\)", open("o7_map_v2_60.out").read())]
def lonely(S):
    def bf(v): return [(Fr(7 * m + 1, 7 * v), Fr(7 * m + 6, 7 * v)) for m in range(v)]
    cur = bf(S[0])
    for v in S[1:]:
        B = bf(v); i = j = 0; out = []
        while i < len(cur) and j < len(B):
            lo, hi = max(cur[i][0], B[j][0]), min(cur[i][1], B[j][1])
            if hi > lo: out.append((lo, hi))
            if cur[i][1] < B[j][1]: i += 1
            else: j += 1
        cur = out
    return cur
def edges(S, x, e):
    return [(k + 1, (x * v - Fr(e, 7))) for k, v in enumerate(S) if (x * v - Fr(e, 7)).denominator == 1]
if __name__ == "__main__":
    print(f"{len(T6)} T6 sets")
    for S in sorted(T6):
        iv = lonely(S); L, U = max(iv, key=lambda z: z[1] - z[0])
        eL = edges(S, L, 1); eU = edges(S, U, 6)
        sl = []
        for k, v in enumerate(S):
            n = (v * L).numerator // (v * L).denominator
            sl.append(f"{k+1}:n{n}/{min(v * L - n - Fr(1, 7), n + Fr(6, 7) - v * U)}")
        print(f"{S}: intervals {len(iv)}  L {L} U {U} len {U - L}  in {[(a, int(m)) for a, m in eL]}"
              f" out {[(a, int(m)) for a, m in eU]}  slack {' '.join(sl)}")
