#!/usr/bin/env python3
"""Prototype of the slow-regime tree for §5 k = 1, alpha <= A1: boxes in (lam, lam5) with lam5 >= lam > 1. A leaf is
(n1, m3, m4, m5, pa, pb) with pb - pa >= A1 such that for every P in [pa, pb] and every (lam, lam5) in the box: runner 1 in
band n1 (P in [n1+1/6, n1+5/6]) and every lower bound <= every upper bound, where bounds (in runner 2's reading) are
1/6, 5/6 (runner 2), m3 + 1/6 - P, m3 + 5/6 - P (runner 3), m4 +- - lam P, m5 +- - lam5 P. Each pairwise condition is
multilinear in (P, lam, lam5): checked at the 8 corners. Leaf search: pa on a grid of step A1/4 over runner-1 bands
n1 = 0, 1, 2; laps from the box centre at the interval centre. Reports leaf counts and failures over the region
lam in (1, LAM], lam5 in [lam, LAM5]."""
import math, sys, itertools
A1 = float(sys.argv[1]) if len(sys.argv) > 1 else 1 / 25
LAM = float(sys.argv[2]) if len(sys.argv) > 2 else 8
LAM5 = float(sys.argv[3]) if len(sys.argv) > 3 else 24
NODECAP = int(sys.argv[4]) if len(sys.argv) > 4 else 4000
def leaf_ok(box, n1, m, pa, pb):
    l0, l1, k0, k1 = box
    if not (n1 + 1 / 6 <= pa and pb <= n1 + 5 / 6): return False
    m3, m4, m5 = m
    for P in (pa, pb):
        for lam in (l0, l1):
            for lam5 in (k0, k1):
                lows = [1 / 6, m3 + 1 / 6 - P, m4 + 1 / 6 - lam * P, m5 + 1 / 6 - lam5 * P]
                ups = [5 / 6, m3 + 5 / 6 - P, m4 + 5 / 6 - lam * P, m5 + 5 / 6 - lam5 * P]
                if max(lows) > min(ups) + 1e-12: return False
    return True
def find(box):
    l0, l1, k0, k1 = box; lc, kc = (l0 + l1) / 2, (k0 + k1) / 2
    for n1 in range(3):
        pa = n1 + 1 / 6
        while pa + A1 <= n1 + 5 / 6 + 1e-12:
            pb = pa + A1; P = (pa + pb) / 2
            for y in [i / 60 for i in range(10, 51)]:   # candidate runner-2 reading at the centre
                m3 = math.floor(y + P - 1 / 6); m4 = math.floor(y + lc * P - 1 / 6); m5 = math.floor(y + kc * P - 1 / 6)
                if leaf_ok(box, n1, (m3, m4, m5), pa, pb): return (n1, (m3, m4, m5), pa, pb)
            pa += A1 / 4
    return None
st = {"leaf": 0, "empty": 0, "fail": 0}; fails = []
stack = [(1.0, LAM, 1.0, LAM5, 0)]
while stack:
    l0, l1, k0, k1, d = stack.pop()
    if k1 < l0: st["empty"] += 1; continue
    if find((l0, l1, k0, k1)): st["leaf"] += 1; continue
    if d > 18 or st['leaf'] + st['fail'] > NODECAP: st["fail"] += 1; fails.append((l0, l1, k0, k1)); continue
    if (l1 - l0) >= (k1 - k0) / 3: m = (l0 + l1) / 2; stack += [(l0, m, k0, k1, d + 1), (m, l1, k0, k1, d + 1)]
    else: m = (k0 + k1) / 2; stack += [(l0, l1, k0, m, d + 1), (l0, l1, m, k1, d + 1)]
print(f"A1 {A1}, lam <= {LAM}, lam5 <= {LAM5}: {st}")
import collections
print("fail boxes by (lam, lam5) rounded:", collections.Counter((round((f[0]+f[1])/2, 1), round((f[2]+f[3])/2, 1)) for f in fails).most_common(15))
