#!/usr/bin/env python3
"""Neighbours of the tight set: v = c (1,3,4,5,9) + (0, d2, d2, d4, d5) (k = 1: v3 = v1 + v2 forces d3 = d2).
Exact-in-floats lonely set over one period t in [0, 1) (integer speeds), as the intersection of the five band lists.
For each lonely interval: its midpoint t, the nearest tight instant t_m = (m + s/6)/c (s = +1 or -1: s=+1 gives the
tight readings (1/6, 1/2, 2/3, 5/6, 1/2), s=-1 the mirror), the offset (t - t_m) c, and the displacement d t_m (mod 1).
Reports per set: the number of lonely intervals, total measure, and the earliest interval's (m, s, displacement)."""
import math, sys
from collections import Counter
EPS = 1e-12
def bands(v, T=1.0):
    return [((m + 1 / 6) / v, (m + 5 / 6) / v) for m in range(int(T * v) + 1)]
def inter(A, B):
    i = j = 0; out = []
    while i < len(A) and j < len(B):
        lo, hi = max(A[i][0], B[j][0]), min(A[i][1], B[j][1])
        if hi > lo + EPS: out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out
def lonely(S):
    cur = bands(S[0])
    for v in S[1:]: cur = inter(cur, bands(v))
    return cur
if __name__ == "__main__":
    rows = []
    for c in range(4, 31):
        for d2 in range(-2, 3):
            for d4 in range(-2, 3):
                for d5 in range(-3, 4):
                    if (d2, d4, d5) == (0, 0, 0): continue
                    S = (c, 3 * c + d2, 4 * c + d2, 5 * c + d4, 9 * c + d5)
                    if not all(S[i] < S[i + 1] for i in range(4)) or math.gcd(*S) != 1: continue
                    iv = lonely(S)
                    if not iv: rows.append((S, 0, None)); continue
                    L, U = iv[0]; t = (L + U) / 2
                    best = None
                    for s in (1, -1):
                        m = round(t * c - s / 6)
                        tm = (m + s / 6) / c
                        if best is None or abs(t - tm) < abs(t - best[2]): best = (m, s, tm)
                    m, s, tm = best
                    disp = tuple(round((dd * tm) % 1, 3) for dd in (0, d2, d2, d4, d5))
                    rows.append((S, len(iv), (m, s, round((t - tm) * c, 4), round((U - L) * c, 4), disp)))
    none = [r for r in rows if r[1] == 0]
    print("neighbours checked:", len(rows), " with no lonely interval:", none[:5])
    print("earliest lonely interval: m/c distribution:", Counter(round(r[2][0] / r[0][0], 1) for r in rows if r[2]).most_common(10))
    print("offset (t - t_m) c of earliest interval (should be small if the witness is a displaced tight instant):",
          Counter(round(r[2][2], 1) for r in rows if r[2]).most_common(8))
    for r in rows[:2] + [r for r in rows if r[0][0] in (20, 29)][:14]: print("  ", r)

