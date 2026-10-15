#!/usr/bin/env python3
"""Why the walk ends early (observation). For each residual set: final state (rank, k) of the walk,
flank x and v1*T = v1(6k+1)/(6x) (or 1/6 if no move). Early = v1*T < 1/3.
Reports: (1) the staircase check -- among walks whose openings are all k = 1, are setter ranks strictly
decreasing (exact consequence of time increasing)?; (2) final-state distribution for early vs late;
(3) for late walks, the final flank ratio x/v1 and k; (4) for early walks ending at (x, 1), whether
x > 3.5 v1 always (exact equivalence check)."""
from fractions import Fraction as F
from collections import Counter
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c = l.split("\t")[:2]
    rows.append((eval(s), c))
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def walk(S):
    t = F(1, 6 * S[0]); path = [(S[0], 0)]
    while True:
        blk = [d for d in S if cd(d * t) < F(1, 6)]
        if not blk: return path, t
        best = None
        for d in blk:
            N = round(d * t); o = F(6 * N + 1, 6 * d)
            if best is None or o > best[0]: best = (o, d, N)
        t = best[0]; path.append((best[1], best[2]))
stair_ok = stair_n = 0; early_final = Counter(); late_final = Counter(); late_info = Counter()
equiv_bad = 0; n_early = n_late = 0
for S, c in rows:
    path, T = walk(S)
    moves = path[1:]
    if moves and all(k == 1 for _, k in moves):
        stair_n += 1; stair_ok += all(a[0] > b[0] for a, b in zip(moves, moves[1:]))
    x, k = path[-1]; v1 = S[0]; early = v1 * T < F(1, 3)
    rank = S.index(x) + 1
    if early:
        n_early += 1; early_final[(rank, k)] += 1
        if k == 1 and not (F(x, v1) > F(7, 2)): equiv_bad += 1
    else:
        n_late += 1; late_final[(rank, k, c)] += 1
        late_info[(k, "x/v1<3.5" if F(x, v1) < F(7, 2) else "x/v1>=3.5")] += 1
print(f"staircase: walks with every move at k=1: {stair_n}; setters strictly decreasing in size: {stair_ok}")
print(f"early (v1*T < 1/3): {n_early}; late: {n_late}")
print("  early final states (rank, k):", early_final.most_common(8))
print(f"  early walks ending at k=1 with x <= 3.5 v1 (should be 0): {equiv_bad}")
print("  late final states (rank, k, BHK case):", late_final.most_common(10))
print("  late walks by (final k, final x/v1):", dict(late_info))
