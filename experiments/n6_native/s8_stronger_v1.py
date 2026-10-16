#!/usr/bin/env python3
"""Observation: which statements cover the §8 remainder R (outside the closed-form cases A-D), from a wide family:
 W: any three-runner block on any laps (t <= 3/v1) with window_two (base + residue) on the other two;
 F: any four-runner block on any laps with the fifth folded alone;
 B: lap boxes (the lap vectors of each sample point's lonely intervals, t <= 3/v1).
Sample: random rational points (x2..x5) of §8 with denominators 97, kept if in R (not A, B, C, D). For each point the set
of statements that close it; greedy smallest list; then the list tested on a fresh sample."""
import random, sys
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 600
def inA(x): return x[3] * (5 - x[2]) >= 4 * x[2]
def inB(x): return x[3] < 5 and x[4] * (5 - x[3]) >= 2 * x[3]
def inC(x): return x[4] <= 5
def inD(x): return x[3] <= 5 and 7 * x[3] <= 5 * x[4] and x[4] <= 11
def sharp(l, a, b):
    if l < F(1, 3) / a + F(1, 3) / b: return False
    m = 0
    while 3 * m * a < a + b:
        if F(3 * m + 1, 3) / b > l: return False
        m += 1
    return True
def windows(vs, tmax):
    out = []
    def rec(i, L, U, ms):
        if L > U or L > tmax: return
        if i == len(vs): out.append((L, U, tuple(ms))); return
        for m in range(int(L * vs[i]), int(tmax * vs[i]) + 1):
            rec(i + 1, max(L, F(6 * m + 1, 6) / vs[i]), min(U, F(6 * m + 5, 6) / vs[i]), ms + [m])
    rec(0, F(0), F(10 ** 9), []); return out
def closing(x):
    res = set(); tmax = F(3)
    for blk in combinations(range(5), 3):
        a, b = [x[i] for i in range(5) if i not in blk]
        for L, U, ms in windows([x[i] for i in blk], tmax):
            if sharp(U - L, a, b): res.add(("W", blk, ms))
    for blk in combinations(range(5), 4):
        r = [i for i in range(5) if i not in blk][0]
        for L, U, ms in windows([x[i] for i in blk], tmax):
            if x[r] * (U - L) >= F(1, 3): res.add(("F", blk, ms))
    pts = sorted(set(F(6 * k + j, 6) / d for d in x for k in range(int(tmax * d) + 1) for j in (1, 5)))
    for a in pts:
        if a <= tmax and all(F(1, 6) <= (d * a) % 1 <= F(5, 6) for d in x):
            res.add(("B", tuple((d * a).numerator // (d * a).denominator for d in x)))
    return res
def sample(n):
    out = []
    while len(out) < n:
        x2 = F(random.randint(97, 291), 97); x3 = F(random.randint(int(x2 * 97), 291), 97)
        x4 = F(random.randint(int(x3 * 97), 6 * 97), 97); x5 = F(random.randint(int(x4 * 97), 13 * 97), 97)
        x = (F(1), x2, x3, x4, x5)
        if not (inA(x) or inB(x) or inC(x) or inD(x)) and x2 < x3 < x4 < x5: out.append(x)
    return out
P = sample(N); cov = {x: closing(x) for x in P}
left = set(P); greedy = []; allc = Counter(s for x in P for s in cov[x])
while left:
    s = max(allc, key=lambda z: sum(1 for x in left if z in cov[x]))
    hit = {x for x in left if s in cov[x]}
    greedy.append((s, len(hit))); left -= hit
print(f"R sample {N}: greedy list {len(greedy)}")
for s, n in greedy: print("   ", n, s)
Q = sample(N); miss = sum(1 for x in Q if not (closing(x) & set(s for s, _ in greedy)))
print(f"fresh sample {N}: not closed by the list: {miss}")
