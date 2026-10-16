#!/usr/bin/env python3
"""Coverage of the proved first-window statements on §8 (primitive 5-sets <= H, v3 <= 3 v1):
 T1 s8_block3_window: 4 v1 v3 <= v4 (5 v1 - v3); T3 s8_block4_fold: 2 v1 v4 <= v5 (5 v1 - v4);
 spread box v5 <= 5 v1; runner-5 second-lap box v4 <= 5 v1, 7 v4 <= 5 v5, v5 <= 11 v1 (both proved, E54).
Counts per statement (first that applies) and the remainder, with the later-window counts from s8_window_v1-v3."""
import math, sys
from itertools import combinations
from collections import Counter
H = int(sys.argv[1]) if len(sys.argv) > 1 else 40
c = Counter(); N = 0
for S in combinations(range(1, H + 1), 5):
    v1, v2, v3, v4, v5 = S
    if v3 > 3 * v1 or math.gcd(*S) != 1: continue
    N += 1
    if 4 * v1 * v3 <= v4 * (5 * v1 - v3): c["T1 three-block window"] += 1
    elif v4 < 5 * v1 and 2 * v1 * v4 <= v5 * (5 * v1 - v4): c["T3 four-block fold"] += 1
    elif v5 <= 5 * v1: c["spread box"] += 1
    elif v4 <= 5 * v1 and 7 * v4 <= 5 * v5 and v5 <= 11 * v1: c["second-lap box"] += 1
    else: c["remaining (later windows or BHK)"] += 1
print(f"H={H}: §8 primitive sets {N}:", dict(c))
