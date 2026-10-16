#!/usr/bin/env python3
"""Float prototype, k = 1 tree with the tight-neighbourhood leaves (E110) and non-strict windows (b >= a):
 TP1: whole box in N1 = {r2 in [14/5, 17/5], r4 <= 29/5, r5 in [43/5, 47/5]};  TP2: in N2 = {r2 <= 11/5, r4 in [19/5, 23/5],
 r5 <= 29/5}, with r2 = 1/alpha, r4 = (1+beta)/alpha, r5 = (1+beta) nu / alpha. Slabs in alpha down to small values, to see
where the tree stops closing."""
import math, sys
src = open("s5k1_cert_v1.py").read().split("slabs = [")[0]
src = src.replace("if b > a + EPS: yield from ext(block, a, b, idx + 1)", "if b >= a - EPS: yield from ext(block, a, b, idx + 1)")
exec(src)
def tp(box):
    a0, a1, k0, k1, b0, b1, n0, n1 = box
    if b1 == INF or n1 == INF: return None
    r2 = (1 / a1, 1 / a0); r4 = ((1 + b0) / a1, (1 + b1) / a0); r5 = ((1 + b0) * n0 / a1, (1 + b1) * n1 / a0)
    if 14 / 5 <= r2[0] and r2[1] <= 17 / 5 and r4[1] <= 29 / 5 and 43 / 5 <= r5[0] and r5[1] <= 47 / 5: return "TP1"
    if r2[1] <= 11 / 5 and 19 / 5 <= r4[0] and r4[1] <= 23 / 5 and r5[1] <= 29 / 5: return "TP2"
    return None
leaf0 = leaf
def leaf(box): return tp(box) or leaf0(box)
lo_slabs = [float(x) for x in sys.argv[1:]] if len(sys.argv) > 1 else [0.005, 0.01, 0.02, 0.04, 0.32, 0.34, 0.45, 0.5]
for a0, a1 in zip(lo_slabs, lo_slabs[1:]):
    st, kinds, fails = run((a0, a1, 1.0, 1.0, 0.0, INF, 1.0, INF), 34, 300000)
    print(f"alpha in [{a0}, {a1}]: {st} {kinds}", flush=True)
    for b in fails[:3]: print("   fail", [round(x, 5) for x in b])
