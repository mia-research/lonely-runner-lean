#!/usr/bin/env python3
"""Stress test of the joint slow closure (o7_joint_v1.closes; exact verification of every closure) on structured
six-runner families in the slow region v5 > 100 v1, v6 < 6 v5:
  runs:     (v1, n, n+d, n+2d, n+3d, n+4d)
  tightK:   (v1, c*P + o) for P a 5-pattern from {(1,2,3,4,5), (1,3,4,5,9), (2,3,4,5,6), (1,2,3,4,6)} and small offsets o
  mixed:    (v1, n, n+1, m, m+1, m+2) two clusters
  random:   v1 up to 60"""
import math, random, sys
from collections import Counter
from o7_joint_v1 import closes
rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
fam = Counter(); bad = []
def test(name, P):
    if len(set(P)) < 6 or list(P) != sorted(P) or math.gcd(*P) != 1 or P[4] <= 100 * P[0] or P[5] >= 6 * P[4]: return
    r = closes(P); fam[(name, bool(r))] += 1
    if not r and len(bad) < 30: bad.append((name, P))
for v1 in (1, 2, 3, 5, 7, 11, 20, 37):
    for n in (150 * v1, 400 * v1, 1000 * v1 + 7):
        for d in (1, 2, 3, 5):
            test("runs", (v1, n, n + d, n + 2 * d, n + 3 * d, n + 4 * d))
        for pat in ((1, 2, 3, 4, 5), (1, 3, 4, 5, 9), (2, 3, 4, 5, 6), (1, 2, 3, 4, 6)):
            for _ in range(6):
                c = n // pat[0]
                o = sorted(rnd.randint(0, 6) for _ in range(5))
                test("tightK", (v1, *(c * p + oo for p, oo in zip(pat, o))))
        for _ in range(6):
            m = n + rnd.randint(3, n)
            test("mixed", (v1, n, n + 1, m, m + 1, m + 2))
for _ in range(400):
    v1 = rnd.randint(1, 60); v5 = rnd.randint(100 * v1 + 1, 100 * v1 + 4000); v6 = rnd.randint(v5 + 1, 6 * v5 - 1)
    test("random", (v1, *sorted(rnd.sample(range(v1 + 1, v5), 3)), v5, v6))
print("closed / not closed by family:", sorted(fam.items()))
print("not closed:", bad)
