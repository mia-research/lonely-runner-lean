#!/usr/bin/env python3
"""Fast regime observation, §5 k = 1, small alpha. Speeds in units of v2: (alpha, 1, 1 + alpha, 1 + beta, 1 + gamma).
For t in runner 1's first band (runner-2 laps j with P = alpha (j + y) in [1/6, 5/6]), the lonely set is computed exactly
(float band intersection). Per (beta, gamma): the number of runner-2 laps j that contain a lonely instant, out of
about 2/(3 alpha) laps, and the share; the (beta, gamma) with the smallest share (resonances)."""
import math, sys
EPS = 0.0
def bands(v, T0, T1):
    out = []
    for m in range(int(T0 * v) - 1, int(T1 * v) + 2):
        a, b = (m + 1 / 6) / v, (m + 5 / 6) / v
        a, b = max(a, T0), min(b, T1)
        if b >= a: out.append((a, b))
    return out
def inter(A, B):
    i = j = 0; out = []
    while i < len(A) and j < len(B):
        lo, hi = max(A[i][0], B[j][0]), min(A[i][1], B[j][1])
        if hi >= lo: out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out
def good_laps(al, be, ga):
    v = [al, 1, 1 + al, 1 + be, 1 + ga]
    T0, T1 = (1 / 6) / al, (5 / 6) / al          # runner 1's first band, in units 1/v2
    cur = bands(v[1], T0, T1)
    for x in v[2:]: cur = inter(cur, bands(x, T0, T1))
    laps = set(int(a) for a, b in cur)
    return len(laps), (T1 - T0)
al = float(sys.argv[1]) if len(sys.argv) > 1 else 0.002
rows = []
for bi in range(1, 51):
    be = 0.51 * bi / 51
    for gi in range(0, 60):
        ga = be + 0.002 + 3.0 * gi / 60
        n, tot = good_laps(al, be, ga)
        rows.append((n / tot, n, round(be, 4), round(ga, 4)))
rows.sort()
print(f"alpha {al}: laps in runner 1's band about {int(2 / (3 * al))}")
print("  (beta, gamma) with the fewest good laps (share, count):")
for r in rows[:25]: print("    ", r)
print("  no good lap at all:", [r for r in rows if r[1] == 0][:10])
