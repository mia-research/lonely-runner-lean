#!/usr/bin/env python3
"""§5 k = 1, alpha <= 1/50, the strip lam in [25/14, 16/5]:
 (S) tree over (lam, lam5) in [25/14, 16/5] x [lam, LAM5] with ivt_box leaves (5 runners, P-interval >= 1/50);
 (R5) for lam5 > LAM5: 4-runner (runners 1..4) ivt_box intervals of length >= 1/(LAM5 - 16/5) + 2/(3 LAM5), as a tree in lam.
Leaf conditions are multilinear in (P, lam, lam5): corners."""
import math, sys
LAM5 = float(sys.argv[1]) if len(sys.argv) > 1 else 40
L0, L1 = 25 / 14, 16 / 5
def ok(n1, m, pa, pb, lam_box, lam5_box):
    if not (n1 + 1 / 6 <= pa and pb <= n1 + 5 / 6): return False
    for P in (pa, pb):
        for lam in lam_box:
            for lam5 in (lam5_box if lam5_box else (None,)):
                lows = [1 / 6, m[0] + 1 / 6 - P, m[1] + 1 / 6 - lam * P]
                ups = [5 / 6, m[0] + 5 / 6 - P, m[1] + 5 / 6 - lam * P]
                if lam5 is not None: lows.append(m[2] + 1 / 6 - lam5 * P); ups.append(m[2] + 5 / 6 - lam5 * P)
                if max(lows) > min(ups) + 1e-12: return False
    return True
def find(lam_box, lam5_box, width):
    lc = sum(lam_box) / 2; kc = sum(lam5_box) / 2 if lam5_box else None
    for n1 in range(3):
        pa = n1 + 1 / 6
        while pa + width <= n1 + 5 / 6 + 1e-12:
            pb = pa + width; P = (pa + pb) / 2
            for y in [i / 120 for i in range(20, 101)]:
                m = [math.floor(y + P - 1 / 6), math.floor(y + lc * P - 1 / 6)]
                if kc is not None: m.append(math.floor(y + kc * P - 1 / 6))
                if ok(n1, m, pa, pb, lam_box, lam5_box): return (n1, m, pa, pb)
            pa += width / 8
    return None
def tree2d():
    st = {"leaf": 0, "empty": 0, "fail": 0}; fails = []; stack = [(L0, L1, L0, LAM5, 0)]
    while stack:
        l0, l1, k0, k1, d = stack.pop()
        if k1 < l0: st["empty"] += 1; continue
        if find((l0, l1), (k0, k1), 1 / 50): st["leaf"] += 1; continue
        if d > 22: st["fail"] += 1; fails.append((l0, l1, k0, k1)); continue
        if (l1 - l0) * 8 >= (k1 - k0): m = (l0 + l1) / 2; stack += [(l0, m, k0, k1, d + 1), (m, l1, k0, k1, d + 1)]
        else: m = (k0 + k1) / 2; stack += [(l0, l1, k0, m, d + 1), (l0, l1, m, k1, d + 1)]
    return st, fails
def tree1d(width):
    st = {"leaf": 0, "fail": 0}; fails = []; stack = [(L0, L1, 0)]
    while stack:
        l0, l1, d = stack.pop()
        if find((l0, l1), None, width): st["leaf"] += 1; continue
        if d > 22: st["fail"] += 1; fails.append((l0, l1)); continue
        m = (l0 + l1) / 2; stack += [(l0, m, d + 1), (m, l1, d + 1)]
    return st, fails
st, f = tree2d(); print(f"(S) lam in [25/14, 16/5], lam5 <= {LAM5}: {st}", [[round(x, 4) for x in b] for b in f[:5]])
w = 1 / (LAM5 - L1) + 2 / (3 * LAM5)
st, f = tree1d(w); print(f"(R5) 4-runner intervals of length {w:.4f}: {st}", [[round(x, 4) for x in b] for b in f[:5]])
