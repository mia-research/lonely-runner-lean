#!/usr/bin/env python3
"""Float prototype (margin EPS) of the §5 k >= 2 large-alpha tree (see s5_cert_v1 for the leaf types).
Box (a0,a1,k0,k1,b0,b1,n0,n1) with b1, n1 possibly inf. Speeds/v2: c1 = alpha, c2 = 1, c3 = 1 + alpha kappa, c4 = 1 + beta,
c5 = (1 + beta) nu. Leaves: W (runners 1,2,3 in bands, (1+b0)(yb-ya) >= 2/3), F(r) (other four in bands, c_r(lo)(yb-ya) >= 1/3).
Prints stats per alpha slab and the failing boxes."""
import math, sys
INF = math.inf; EPS = 1e-9
def band(m, lo, hi):
    if hi == INF: return None
    return ((m + 1 / 6) / lo, (m + 5 / 6) / hi)
def laps(L, U, lo, hi):
    return range(max(0, math.floor(L * lo) - 1), math.floor(U * hi) + 2)
def leaf(box):
    a0, a1, k0, k1, b0, b1, n0, n1 = box
    lo = [a0, 1, 1 + a0 * k0, 1 + b0, (1 + b0) * n0]
    hi = [a1, 1, 1 + a1 * k1, 1 + b1, (1 + b1) * n1]
    def ext(block, L, U, idx):
        """extend a window by the remaining block runners; yield (L, U) windows"""
        if idx == len(block): yield L, U; return
        i = block[idx]
        if hi[i] == INF: return
        for m in laps(L, U, lo[i], hi[i]):
            I = band(m, lo[i], hi[i]); a, b = max(L, I[0]), min(U, I[1])
            if b > a + EPS: yield from ext(block, a, b, idx + 1)
    for n1_ in range(3):
        I1 = band(n1_, lo[0], hi[0])
        if I1[1] <= I1[0]: continue
        for L, U in ext([2, 1], I1[0], I1[1], 0):   # runners 3, 2
            if (1 + b0) * (U - L) >= 2 / 3 + EPS: return "W"
            for a, b in ext([3], L, U, 0):
                if lo[4] * (b - a) >= 1 / 3 + EPS: return "F5"
            if lo[3] * (U - L) >= 1 / 3 + EPS:
                for a, b in ext([4], L, U, 0):
                    if lo[3] * (b - a) >= 1 / 3 + EPS: return "F4"
        for blk, r in (([1, 3, 4], 2), ([2, 3, 4], 1)):
            for a, b in ext(blk, I1[0], I1[1], 0):
                if lo[r] * (b - a) >= 1 / 3 + EPS: return f"F{r+1}"
    return None
def empty(box):
    a0, a1, k0, k1, b0, b1, n0, n1 = box
    return 3 * a0 >= 1 + a0 * k1 - EPS or b1 <= a0 * k0 + EPS
def split(box):
    a0, a1, k0, k1, b0, b1, n0, n1 = box
    if b1 == INF: return [(a0, a1, k0, k1, b0, max(1, 2 * b0), n0, n1), (a0, a1, k0, k1, max(1, 2 * b0), INF, n0, n1)]
    if n1 == INF: nm = max(2, 2 * n0); return [(a0, a1, k0, k1, b0, b1, n0, nm), (a0, a1, k0, k1, b0, b1, nm, INF)]
    wa = (a1 - a0) / a1 * 4; wk = (k1 - k0) * 2; wb = (b1 - b0) / (1 + b1) * 3; wn = (n1 - n0) / n1 * 2
    w = max(wa, wk, wb, wn)
    if w == wa: m = (a0 + a1) / 2; return [(a0, m, k0, k1, b0, b1, n0, n1), (m, a1, k0, k1, b0, b1, n0, n1)]
    if w == wk: m = (k0 + k1) / 2; return [(a0, a1, k0, m, b0, b1, n0, n1), (a0, a1, m, k1, b0, b1, n0, n1)]
    if w == wb: m = (b0 + b1) / 2; return [(a0, a1, k0, k1, b0, m, n0, n1), (a0, a1, k0, k1, m, b1, n0, n1)]
    m = (n0 + n1) / 2; return [(a0, a1, k0, k1, b0, b1, n0, m), (a0, a1, k0, k1, b0, b1, m, n1)]
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
lo_a = float(sys.argv[1]) if len(sys.argv) > 1 else 0.04
slabs = [lo_a, 0.06, 0.08, 0.1, 0.13, 0.16, 0.2, 0.25, 0.3, 0.35, 0.4]
for a0, a1 in zip(slabs, slabs[1:]):
    st, kinds, fails = run((a0, a1, 0.0, 0.5, 0.0, INF, 1.0, INF), 40, 300000)
    print(f"alpha in [{a0}, {a1}]: {st} {kinds}", flush=True)
    for b in fails[:4]: print("   fail", [round(x, 5) for x in b], flush=True)
