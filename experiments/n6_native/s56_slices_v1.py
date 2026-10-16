#!/usr/bin/env python3
"""Observation only. §5 and §6 as integer-indexed slices of ratio space (x_i = v_i / v_1):
  §6: D | v3, v3 = c D, v2 = (c-1) D  ->  x2 = x3 (c-1)/c  (one slice per c >= 2);
  §5: v1 = c' D                        ->  x3 - x2 = 1/c'   (one slice per c' >= 1).
For every primitive set <= H in §5/§6: its slice index, and the statements (W any 3-block on any laps with window_two;
F any 4-block on any laps with a fold; t <= 3/v1) that close it. Per slice index: the commonest statements, and the
laps expressed against floor(x_r * T) at the window's start T = L v1 (do laps follow the ratios?)."""
import math, sys
from fractions import Fraction as F
from itertools import combinations
from collections import Counter, defaultdict
H = int(sys.argv[1]) if len(sys.argv) > 1 else 30
exec(open("s56_window_v1.py").read().split("sets = [")[0])
H = int(sys.argv[1]) if len(sys.argv) > 1 else 30
by = defaultdict(Counter); nset = Counter(); uncl = Counter()
for S in combinations(range(1, H + 1), 5):
    if math.gcd(*S) != 1: continue
    c = case(S)
    if not c: continue
    D = S[2] - S[1]
    idx = (c, S[2] // D if c == "S6" else S[0] // D)
    nset[idx] += 1
    ts = types_closing(S)
    if not ts: uncl[idx] += 1
    for t in ts: by[idx][t] += 1
for idx in sorted(nset, key=lambda z: (z[0], z[1]))[:16]:
    top = by[idx].most_common(4)
    print(f"{idx[0]} index {idx[1]}: {nset[idx]} sets, unclosed {uncl[idx]}; top statements (sets closed): {[(t, n) for t, n in top]}")
