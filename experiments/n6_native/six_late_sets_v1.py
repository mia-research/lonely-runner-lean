#!/usr/bin/env python3
"""E26: all primitive 5-sets in [1,H] whose earliest lonely instant is past the slowest runner's first lap
(tau = d_min*T >= 7/6). For each: tau, lap vector of the earliest box, and whether the box (1,3,4,5,7) is alive,
with its pair slacks (6k_j+5)d_i - (6k_i+1)d_j that are smallest. Uses the C enumerator's criterion in Python on
the candidate range only (spread in [5,7), which the C run shows contains every such set up to 120).
Usage: six_late_sets_v1.py H"""
import sys
from fractions import Fraction as F
from math import gcd
from collections import Counter
H = int(sys.argv[1])
def earliest(s):
    best = None
    for b in s:
        for k in range(b):
            if best is not None and F(6*k+1, 6*b) >= best[0]: break
            if all(b <= a*(6*k+1) % (6*b) <= 5*b for a in s):
                best = (F(6*k+1, 6*b), b, k); break
    return best
K0 = (1, 3, 4, 5, 7)
def slacks(s, k):
    return sorted(((6*k[j]+5)*s[i] - (6*k[i]+1)*s[j], i+1, j+1) for i in range(5) for j in range(5) if i != j)
laps = Counter(); out = []
for a1 in range(1, H+1):
    for a5 in range(5*a1, min(7*a1, H+1)):
        for a2 in range(a1+1, a5):
            for a3 in range(a2+1, a5):
                for a4 in range(a3+1, a5):
                    s = (a1, a2, a3, a4, a5)
                    if gcd(gcd(gcd(a1, a2), gcd(a3, a4)), a5) != 1: continue
                    T, b, k = earliest(s)
                    tau = a1 * T
                    if tau < F(7, 6): continue
                    t = T
                    lv = tuple(int(x*t - F(1, 6)) if x*t >= F(1,6) else 0 for x in s)
                    lv = tuple((x*(6*k+1) - b) // (6*b) if False else int((x*t*6 - 1) // 6) for x in s)
                    laps[lv] += 1
                    sl = slacks(s, K0)
                    out.append((s, tau, lv, sl[0][0] >= 0, sl[:3]))
for s, tau, lv, alive, sl in out: print(s, f"tau={tau}={float(tau):.4f}", "laps", lv, "box(1,3,4,5,7) alive" if alive else "box(1,3,4,5,7) DEAD", sl)
print(f"H={H}: late sets {len(out)}; lap vectors {dict(laps)}; box (1,3,4,5,7) alive in {sum(1 for o in out if o[3])}")
