#!/usr/bin/env python3
"""Observation, §5 with k = 1 (D = v1, v3 = v1 + v2, so x3 = x1 + x2 at every instant). Runners 1, 2, 3 are clear exactly when
(x1, {x2}) lies in T_same (x1 + {x2} <= 5/6; runners 2, 3 on one lap) or T_apart (x1 + {x2} >= 7/6; runner 3 one lap
ahead), with x1 in its band. Per set, all closing windows with t <= 3/v1, typed:
  W123:s / W123:a  block {1,2,3} (triangle same / apart) with window_two on 4, 5 (sharp);
  F5:s/a, F4:s/a   block {1,2,3,4} (5 folded) / {1,2,3,5} (4 folded), by triangle;
  F3               block {1,2,4,5}, runner 3 folded;   F2, F1   runner 2 / runner 1 folded;   BOX  all five in bands.
Reports: how often each type is available; the share closed by the 123-triangle types alone, by F3 alone, by their union;
and the sets closed by neither (examples)."""
import math, sys, random
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
exec(open("s56_window_v1.py").read().split("sets = [")[0])
def k1(S):
    v1, v2, v3 = S[:3]
    return v3 - v2 == v1 and v3 > 3 * v1
def types(S):
    v1, v2, v3, v4, v5 = S; tmax = F(3, v1); out = set()
    for L, U, ms in windows([v1, v2, v3], tmax):
        tri = "s" if ms[2] == ms[0] + ms[1] else ("a" if ms[2] == ms[0] + ms[1] + 1 else "?")
        if sharp(U - L, v4, v5): out.add("W123:" + tri)
        for (x, y, nm) in ((v4, v5, "F5"), (v5, v4, "F4")):
            if y * (U - L) < F(1, 3): continue
            for m in range(max(0, math.floor(L * x) - 1), math.floor(U * x) + 2):
                lo, hi = max(L, F(6 * m + 1, 6 * x)), min(U, F(6 * m + 5, 6 * x))
                if hi > lo and y * (hi - lo) >= F(1, 3): out.add(nm + ":" + tri); break
    for blk, nm in (((0, 1, 3, 4), "F3"), ((0, 2, 3, 4), "F2"), ((1, 2, 3, 4), "F1")):
        r = [i for i in range(5) if i not in blk][0]
        for L, U, ms in windows([S[i] for i in blk], tmax):
            if S[r] * (U - L) >= F(1, 3): out.add(nm); break
    if windows(list(S), tmax): out.add("BOX")
    return out
def run(sets, label):
    av = Counter(); c = Counter(); ex = []
    for S in sets:
        ts = types(S)
        for t in ts: av[t] += 1
        tri = any(t.startswith(("W123", "F5", "F4")) for t in ts)
        f3 = "F3" in ts
        key = ("123-triangle" if tri else "") + (" + F3" if f3 else "") if (tri or f3) else ("other: " + ",".join(sorted(ts)) if ts else "NONE")
        c[key if (tri or f3) else ("other" if ts else "NONE")] += 1
        if not tri and len(ex) < 12: ex.append((S, sorted(ts)))
    print(f"== {label}: {len(sets)} sets")
    print("   available:", dict(sorted(av.items(), key=lambda z: -z[1])))
    print("   closed by:", dict(c))
    print("   no 123-triangle window:", ex)
H = int(sys.argv[1]) if len(sys.argv) > 1 else 40
run([S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and k1(S)], f"primitive §5 k=1 <= {H}")
random.seed(51); big = []
while len(big) < 1500:
    v1 = random.randint(1, 600); v2 = random.randint(2 * v1 + 1, 2000); v3 = v1 + v2
    v4 = random.randint(v3 + 1, 3 * v3); v5 = random.randint(v4 + 1, 4 * v3)
    S = (v1, v2, v3, v4, v5)
    if math.gcd(*S) == 1: big.append(S)
run(big, "random §5 k=1")
