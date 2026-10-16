#!/usr/bin/env python3
"""Observation, §5 sets not closed by pair windows (s5_obs_v1 classes D, E, F), by k = v1/D.
For each: every closing four-block fold (block, laps) with t <= 3/v1, and the first one (smallest window start);
recorded: the block (which runner is folded), m3 - m2 (meetings of runners 2, 3 passed, i.e. which interval between
meeting times n/D the window lies in), whether runner 1 is on its first lap, and for k = 1 the 123 window type:
runner 1 reads x1, runner 2 x2, runner 3 x3 = x1 + x2 (sum relation)."""
import math, sys, random
from fractions import Fraction as F
from itertools import combinations
from collections import Counter, defaultdict
exec(open("s5_obs_v1.py").read().split("\ndef run(sets")[0])
def folds(S):
    tmax = F(3, S[0]); out = []
    for blk in combinations(range(5), 4):
        r = [i for i in range(5) if i not in blk][0]
        for L, U, ms in windows([S[i] for i in blk], tmax):
            if S[r] * (U - L) >= F(1, 3): out.append((L, blk, ms, r))
    return sorted(out)
def run(sets, label):
    cnt = defaultdict(Counter); ex = defaultdict(list)
    for S in sets:
        v1, v2, v3 = S[:3]; D = v3 - v2; k = v1 // D; kb = str(k) if k <= 2 else ">=3"
        how, _ = classify(S)
        if how not in ("D", "E", "F"): continue
        fs = folds(S)
        if not fs: cnt[kb]["no fold (" + how + ")"] += 1; ex[(kb, how)].append(S) if len(ex[(kb, how)]) < 10 else None; continue
        L, blk, ms, r = fs[0]
        d = dict(zip(blk, ms))
        m23 = (d[2] - d[1]) if (1 in d and 2 in d) else "n/a"
        cnt[kb][f"folded runner {r + 1}, m3-m2 = {m23}, m1 = {d.get(0, 'n/a')}"] += 1
    print(f"== {label}")
    for kb in sorted(cnt): print(f"   k = {kb}:", sorted(cnt[kb].items(), key=lambda z: -z[1])[:10])
    for key in sorted(ex): print("   examples", key, ex[key])
H = int(sys.argv[1]) if len(sys.argv) > 1 else 36
run([S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and s5(S)], f"primitive §5 <= {H}, not closed by pair windows")
random.seed(55); big = []
while len(big) < 2000:
    S = tuple(sorted(random.sample(range(1, 2001), 5)))
    if math.gcd(*S) == 1 and s5(S): big.append(S)
run(big, "random §5 <= 2000, not closed by pair windows")
