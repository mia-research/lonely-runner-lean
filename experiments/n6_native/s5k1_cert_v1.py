#!/usr/bin/env python3
"""Prototype of the §5 k = 1 tree: s5_cert_v2's float search with kappa fixed at 1 (c3 = 1 + alpha). Domain:
alpha < 1/2 (3 v1 < v3 = v1 + v2), beta > alpha (v4 > v3), nu > 1. Boxes (a0,a1,b0,b1,n0,n1); slabs in alpha.
Reports per slab: leaves by kind, failures, and the failing boxes nearest the tight point (1/3, 2/3, 9/5)."""
import math, sys
exec(open("s5_cert_v2.py").read().split("def empty(box):")[0])
def empty(box):
    a0, a1, k0, k1, b0, b1, n0, n1 = box
    return 2 * a0 >= 1 - EPS or b1 <= a0 + EPS
def split(box):
    a0, a1, k0, k1, b0, b1, n0, n1 = box
    wa = (a1 - a0) / a1 * 4
    if b1 == INF:
        if b0 >= 1 and wa > 0.02: m = (a0 + a1) / 2; return [(a0, m, 1, 1, b0, b1, n0, n1), (m, a1, 1, 1, b0, b1, n0, n1)]
        return [(a0, a1, 1, 1, b0, max(1, 2 * b0), n0, n1), (a0, a1, 1, 1, max(1, 2 * b0), INF, n0, n1)]
    wb = (b1 - b0) / (1 + b1) * 3
    if n1 == INF:
        if max(wa, wb) > 0.02 and n0 >= 2:
            if wa >= wb: m = (a0 + a1) / 2; return [(a0, m, 1, 1, b0, b1, n0, n1), (m, a1, 1, 1, b0, b1, n0, n1)]
            m = (b0 + b1) / 2; return [(a0, a1, 1, 1, b0, m, n0, n1), (a0, a1, 1, 1, m, b1, n0, n1)]
        nm = max(2, 2 * n0); return [(a0, a1, 1, 1, b0, b1, n0, nm), (a0, a1, 1, 1, b0, b1, nm, INF)]
    wn = (n1 - n0) / n1 * 2; w = max(wa, wb, wn)
    if w == wa: m = (a0 + a1) / 2; return [(a0, m, 1, 1, b0, b1, n0, n1), (m, a1, 1, 1, b0, b1, n0, n1)]
    if w == wb: m = (b0 + b1) / 2; return [(a0, a1, 1, 1, b0, m, n0, n1), (a0, a1, 1, 1, m, b1, n0, n1)]
    m = (n0 + n1) / 2; return [(a0, a1, 1, 1, b0, b1, n0, m), (a0, a1, 1, 1, b0, b1, m, n1)]
def run(root, maxdepth, cap):
    st = {"leaf": 0, "empty": 0, "fail": 0}; fails = []; stack = [(root, 0)]; kinds = {}
    while stack:
        box, d = stack.pop()
        if empty(box): st["empty"] += 1; continue
        l = leaf(box)
        if l: st["leaf"] += 1; kinds[l] = kinds.get(l, 0) + 1; continue
        if d >= maxdepth or st["leaf"] + st["fail"] > cap: st["fail"] += 1; fails.append(box); continue
        for b in split(box): stack.append((b, d + 1))
    return st, kinds, fails
slabs = [0.04, 0.06, 0.08, 0.1, 0.13, 0.16, 0.2, 0.25, 0.3, 0.32, 0.34, 0.37, 0.4, 0.45, 0.5]
for a0, a1 in zip(slabs, slabs[1:]):
    st, kinds, fails = run((a0, a1, 1.0, 1.0, 0.0, INF, 1.0, INF), 34, 200000)
    print(f"alpha in [{a0}, {a1}]: {st} {kinds}", flush=True)
    if fails:
        fails.sort(key=lambda b: abs((b[0] + b[1]) / 2 - 1 / 3) + abs((b[4] + (b[5] if b[5] < INF else b[4])) / 2 - 2 / 3))
        for b in fails[:3]: print("   fail", [round(x, 5) for x in b])
        far = [b for b in fails if abs((b[0] + b[1]) / 2 - 1 / 3) > 0.02 or (b[5] < INF and abs((b[4] + b[5]) / 2 - 2 / 3) > 0.05)]
        print("   fails away from the tight point:", len(far), [[round(x, 4) for x in b] for b in far[:3]])
