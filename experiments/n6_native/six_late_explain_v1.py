#!/usr/bin/env python3
"""Late walks ([1,40], v1*T >= 1/3): classify each by exact cause, with checks.
 BOUNDARY: v1(6k+1) = 2x exactly at the final state (x, k) -- 'late' only because the criterion is >=.
 SLOW END: final k = 1 and v1*7 > 2x... i.e. 7 v1 >= 2x (x <= 3.5 v1): the staircase reached a slow flank.
   Check every staircase step at opening 1 (y after x, both at lap 1) satisfies 5x < 7y < 7x
   (opening_one_blocks_iff), and record the number of steps from the first move.
 HIGH LAP: final k >= 2. Record how lap >= 2 was first reached: a first move at lap >= 2 (the start
   ratio v/v1 lies in (11,13) or beyond), a return (setter seen before), or a fresh setter at lap >= 2.
Every late walk must land in exactly one class."""
from fractions import Fraction as F
from collections import Counter
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def walk(S):
    t = F(1, 6 * S[0]); states = []
    while True:
        blk = [d for d in S if cd(d * t) < F(1, 6)]
        if not blk: return states, t
        best = None
        for d in blk:
            N = round(d * t); o = F(6 * N + 1, 6 * d)
            if best is None or o > best[0]: best = (o, d, N)
        t = best[0]; states.append((best[1], best[2]))
cls = Counter(); stair_bad = 0; stair_steps = Counter(); high_how = Counter(); total = 0
for S in rows:
    st, T = walk(S); v1 = S[0]
    if v1 * T < F(1, 3): continue
    total += 1
    x, k = st[-1] if st else (v1, 0)
    if v1 * (6 * k + 1) == 2 * x: cls["BOUNDARY"] += 1; continue
    if k <= 1:
        cls["SLOW END"] += 1
        run = 0
        for (a, p), (b, q) in zip(st, st[1:]):
            if p == 1 and q == 1:
                run += 1
                stair_bad += not (5 * a < 7 * b < 7 * a)
        stair_steps[len(st)] += 1
    else:
        cls["HIGH LAP"] += 1
        seen = set(); how = None
        for i, (d, p) in enumerate(st):
            if p >= 2:
                how = "first move at lap>=2" if i == 0 else ("return" if d in seen else "fresh setter at lap>=2")
                break
            seen.add(d)
        high_how[how] += 1
print(f"late walks: {total}; classes: {dict(cls)}")
print(f"  SLOW END: staircase steps violating 5x < 7y < 7x: {stair_bad}; number of moves in these walks: {dict(sorted(stair_steps.items()))}")
print(f"  HIGH LAP: how lap >= 2 was first reached: {dict(high_how)}")
