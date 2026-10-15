#!/usr/bin/env python3
"""Late walks (v1*T >= 1/3), observation. For each:
 - the first step that lands at an opening index k >= 2: the state before it (rank, k), the elements in
   the way there (ranks), and the setter (rank) with its index N; whether the setter at that step had
   been a setter before (a RETURN) or is new; whether the first move from (1,0) already lands at k >= 2;
 - for walks ending at opening 1 of a flank x < 3.5 v1: the final flank rank and the BHK case.
From six_cascade_observe_v1.tsv; exact Fractions."""
from fractions import Fraction as F
from collections import Counter
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c = l.split("\t")[:2]
    rows.append((eval(s), c))
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def walk(S):
    t = F(1, 6 * S[0]); steps = []   # (state_before, blockers, setter, N)
    state = (1, 0)
    while True:
        blk = [d for d in S if cd(d * t) < F(1, 6)]
        if not blk: return steps, t
        best = None
        for d in blk:
            N = round(d * t); o = F(6 * N + 1, 6 * d)
            if best is None or o > best[0]: best = (o, d, N)
        steps.append((state, tuple(S.index(d) + 1 for d in blk), S.index(best[1]) + 1, best[2]))
        t = best[0]; state = (S.index(best[1]) + 1, best[2])
first_high = Counter(); immediate = 0; returns = 0; n_high = 0; slow_end = Counter(); late = 0
for S, c in rows:
    steps, T = walk(S)
    if S[0] * T < F(1, 3): continue
    late += 1
    hi = next((i for i, st in enumerate(steps) if st[3] >= 2), None)
    if hi is not None:
        n_high += 1
        before, blk, setter, N = steps[hi]
        first_high[(before, blk, setter, N)] += 1
        immediate += hi == 0
        returns += setter in {s[2] for s in steps[:hi]}
    else:
        x_rank = steps[-1][2] if steps else 1
        slow_end[(x_rank, c)] += 1
print(f"late walks: {late}; with some move to k >= 2: {n_high}; that move is the first move from (1,0): {immediate}; "
      f"its setter had set an earlier move (a return): {returns}")
print("  (state before, elements in the way, setter, N) at the first k>=2 move, most common:")
for k, v in first_high.most_common(12): print("    ", k, v)
print("  late walks with all moves at k <= 1, by (final flank rank, BHK case):", dict(slow_end))
