#!/usr/bin/env python3
"""Observation only. The open §8 region of E83: points (primitive integer 5-sets, v3 <= 3 v1) closed by none of the
finite list (windows W3 on laps (0,0,0),(1,2,3),(0,1,1),(0,0,1); fold F4 on (0,0,0,0); boxes (0,0,0,0,0),
(0,0,0,0,1),(0,0,0,1,1),(0,0,1,1,2),(0,1,2,3,4)). Dense enumeration inside the H=60 bounding box of ratios
(v2/v1 in [3/2, 8/3], v3/v1 in [5/2, 3], v4/v1 in [7/2, 6], v5/v1 in [5, 12]) for v1 <= V1.
For each open point: every lonely lap vector with t <= 3/v1 (from the exact lonely intervals of the five runners),
so every lap box containing it. Then a greedy cover of the open points by lap boxes, and the same cover tested on a
denser set (larger V1)."""
import math, sys
from fractions import Fraction as F
from collections import Counter
exec(open("s8_coverage_v2.py").read().split("c = Counter()")[0].replace("H = int(sys.argv[1]) if len(sys.argv) > 1 else 40", "H = 0"))
def closed(S):
    v1, v2, v3, v4, v5 = S
    for laps in W3:
        w = win(S[:3], laps)
        if w and sharp(w[1] - w[0], v4, v5): return True
    w = win(S[:4], (0, 0, 0, 0))
    if w and v5 * (w[1] - w[0]) >= F(1, 3): return True
    return any(box(S, k) for k in BX)
def points(V1):
    for v1 in range(1, V1 + 1):
        for v2 in range(math.ceil(F(3, 2) * v1), math.floor(F(8, 3) * v1) + 1):
            for v3 in range(max(v2 + 1, math.ceil(F(5, 2) * v1)), 3 * v1 + 1):
                for v4 in range(max(v3 + 1, math.ceil(F(7, 2) * v1)), 6 * v1 + 1):
                    for v5 in range(max(v4 + 1, 5 * v1), 12 * v1 + 1):
                        S = (v1, v2, v3, v4, v5)
                        if math.gcd(*S) == 1 and not closed(S): yield S
def lonely_laps(S, tmax):
    pts = sorted(set([F(0), tmax] + [F(6 * k + j, 6 * d) for d in S for k in range(int(tmax * d) + 1) for j in (1, 5)]))
    out = set()
    for a in pts:
        if a <= tmax and all(F(1, 6) <= (d * a) % 1 <= F(5, 6) for d in S):
            out.add(tuple((d * a).numerator // (d * a).denominator for d in S))
    return out
V1 = int(sys.argv[1]) if len(sys.argv) > 1 else 14
V2 = int(sys.argv[2]) if len(sys.argv) > 2 else 20
P = list(points(V1)); print(f"open points with v1 <= {V1}: {len(P)}")
boxes = {S: lonely_laps(S, F(3, S[0])) for S in P}
print("points with no lonely lap vector for t <= 3/v1:", sum(1 for S in P if not boxes[S]))
cnt = Counter(k for S in P for k in boxes[S])
print("lap boxes containing the most open points:", cnt.most_common(10))
left = set(P); cover = []
while left:
    k = max(cnt, key=lambda k: sum(1 for S in left if k in boxes[S]))
    hit = {S for S in left if k in boxes[S]}
    if not hit: break
    cover.append((k, len(hit))); left -= hit
print("greedy cover:", cover, "uncovered:", len(left))
CK = [k for k, _ in cover]
Q = list(points(V2)); miss = [S for S in Q if not any(box(S, k) for k in CK)]
print(f"cover tested on open points with v1 <= {V2}: {len(Q)} points, {len(miss)} not covered", miss[:10])
for i in range(1, 5):
    xs = [F(s[i], s[0]) for s in Q]; print(f"   v{i+1}/v1 over open points (v1 <= {V2}): [{min(xs)}, {max(xs)}]")
