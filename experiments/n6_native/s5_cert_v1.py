#!/usr/bin/env python3
"""Prototype: §5, k >= 2, alpha = v1/v2 >= A1. Speeds / v2: c1 = alpha, c2 = 1, c3 = 1 + alpha*kappa (kappa = 1/k),
c4 = 1 + beta, c5 = (1 + beta)*nu (nu = v5/v4). Domain: 0 <= kappa <= 1/2, A1 <= alpha, 3 alpha < 1 + alpha kappa,
beta > alpha kappa, nu > 1. Boxes [a0,a1] x [k0,k1] x [b0,b1] x [n0,n1] (b1, n1 may be INF).
Leaf types (window [ya, yb] in runner-2 reading y = v2 t):
  F(r, laps): the four runners other than r read in their lap bands at both ends for every point of the box (lower ends
     checked with the smallest c_i, upper ends with the largest), and c_r(lo) (yb - ya) >= 1/3 (runner r folded);
  W(laps): runners 1, 2, 3 in bands, (1 + b0)(yb - ya) >= 2/3 (window_two on runners 4, 5; needs only v4 <= v5).
Empty: 3 a0 >= 1 + a0 k1, or b1 <= a0 k0 (beta > alpha kappa impossible).
Search: for runner 1 laps n1 = 0..2 and runner 2 laps in range, intersect the robust band intervals of the block."""
import math, sys
from fractions import Fraction as F
INF = None
def cs(box):
    (a0, a1), (k0, k1), (b0, b1), (n0, n1) = box
    lo = [a0, F(1), 1 + a0 * k0, 1 + b0, (1 + b0) * n0]
    hi = [a1, F(1), 1 + a1 * k1, None if b1 is INF else 1 + b1, None if (b1 is INF or n1 is INF) else (1 + b1) * n1]
    return lo, hi
def band_iv(m, lo, hi):
    """y-interval on which a runner with speed in [lo, hi] reads in [m+1/6, m+5/6] for every speed: [(m+1/6)/lo, (m+5/6)/hi]"""
    if hi is None: return None
    return (F(6 * m + 1, 6) / lo, F(6 * m + 5, 6) / hi)
def find_leaf(box):
    lo, hi = cs(box)
    best = None
    for n1 in range(0, 3):
        I1 = band_iv(n1, lo[0], hi[0])
        if I1[0] > I1[1]: continue
        for m2 in range(math.floor(I1[0] * lo[1]) - 1, math.floor(I1[1] * hi[1]) + 1):
            if m2 < 0: continue
            I2 = band_iv(m2, lo[1], hi[1])
            L, U = max(I1[0], I2[0]), min(I1[1], I2[1])
            if L >= U: continue
            # runner 3 laps
            for m3 in range(math.floor(L * lo[2]) - 1, math.floor(U * hi[2]) + 2):
                if m3 < 0: continue
                I3 = band_iv(m3, lo[2], hi[2]); L3, U3 = max(L, I3[0]), min(U, I3[1])
                if L3 >= U3: continue
                # W leaf
                if (1 + box[2][0]) * (U3 - L3) >= F(2, 3): return ("W", (n1, m2, m3), L3, U3)
                # F with runner 5 folded: runner 4 in block
                if hi[3] is not None:
                    for m4 in range(math.floor(L3 * lo[3]) - 1, math.floor(U3 * hi[3]) + 2):
                        I4 = band_iv(m4, lo[3], hi[3]); a, b = max(L3, I4[0]), min(U3, I4[1])
                        if a < b and lo[4] * (b - a) >= F(1, 3): return ("F5", (n1, m2, m3, m4), a, b)
                        # runner 5 in block too? then fold one of 1,2,3 -- handled below
                # F with runner 4 folded: runner 5 in block
                if hi[4] is not None and lo[3] * (U3 - L3) >= F(1, 3):
                    for m5 in range(math.floor(L3 * lo[4]) - 1, math.floor(U3 * hi[4]) + 2):
                        I5 = band_iv(m5, lo[4], hi[4]); a, b = max(L3, I5[0]), min(U3, I5[1])
                        if a < b and lo[3] * (b - a) >= F(1, 3): return ("F4", (n1, m2, m3, m5), a, b)
            # runner 3 folded / runner 2 folded / runner 1 folded: blocks with 4 and 5
            if hi[3] is not None and hi[4] is not None:
                for m4 in range(math.floor(L * lo[3]) - 1, math.floor(U * hi[3]) + 2):
                    I4 = band_iv(m4, lo[3], hi[3]); L4, U4 = max(L, I4[0]), min(U, I4[1])
                    if L4 >= U4: continue
                    for m5 in range(math.floor(L4 * lo[4]) - 1, math.floor(U4 * hi[4]) + 2):
                        I5 = band_iv(m5, lo[4], hi[4]); a, b = max(L4, I5[0]), min(U4, I5[1])
                        if a < b and lo[2] * (b - a) >= F(1, 3): return ("F3", (n1, m2, m4, m5), a, b)
    # runner 2 folded: block 1, 3, 4, 5
    if hi[3] is not None and hi[4] is not None:
        for n1 in range(0, 3):
            I1 = band_iv(n1, lo[0], hi[0])
            for m3 in range(math.floor(I1[0] * lo[2]) - 1, math.floor(I1[1] * hi[2]) + 1):
                if m3 < 0: continue
                I3 = band_iv(m3, lo[2], hi[2]); L, U = max(I1[0], I3[0]), min(I1[1], I3[1])
                if L >= U: continue
                for m4 in range(math.floor(L * lo[3]) - 1, math.floor(U * hi[3]) + 2):
                    I4 = band_iv(m4, lo[3], hi[3]); L4, U4 = max(L, I4[0]), min(U, I4[1])
                    if L4 >= U4: continue
                    for m5 in range(math.floor(L4 * lo[4]) - 1, math.floor(U4 * hi[4]) + 2):
                        I5 = band_iv(m5, lo[4], hi[4]); a, b = max(L4, I5[0]), min(U4, I5[1])
                        if a < b and lo[1] * (b - a) >= F(1, 3): return ("F2", (n1, m3, m4, m5), a, b)
    return None
def empty(box):
    (a0, a1), (k0, k1), (b0, b1), (n0, n1) = box
    return 3 * a0 >= 1 + a0 * k1 or (b1 is not INF and b1 <= a0 * k0)
stats = {"leaf": 0, "empty": 0, "fail": 0, "nodes": 0}
fails = []
BMAX_SPLIT = [F(1, 2), F(1), F(2)]; NU_SPLIT = [F(5, 4), F(2), F(4)]
def split(box):
    (a0, a1), (k0, k1), (b0, b1), (n0, n1) = box
    if b1 is INF:
        return [((a0, a1), (k0, k1), (b0, F(1)), (n0, n1)), ((a0, a1), (k0, k1), (F(1), INF), (n0, n1))] if b0 < 1 else None
    if n1 is INF:
        nm = n0 * 2 if n0 >= 2 else F(2)
        return [((a0, a1), (k0, k1), (b0, b1), (n0, nm)), ((a0, a1), (k0, k1), (b0, b1), (nm, INF))]
    # widest relative
    wa = (a1 - a0) / a1 * 4; wk = (k1 - k0) * 2; wb = (b1 - b0) / (1 + b1) * 3; wn = (n1 - n0) / n1 * 2
    w = max(wa, wk, wb, wn)
    if w == wa: m = (a0 + a1) / 2; return [((a0, m), (k0, k1), (b0, b1), (n0, n1)), ((m, a1), (k0, k1), (b0, b1), (n0, n1))]
    if w == wk: m = (k0 + k1) / 2; return [((a0, a1), (k0, m), (b0, b1), (n0, n1)), ((a0, a1), (m, k1), (b0, b1), (n0, n1))]
    if w == wb: m = (b0 + b1) / 2; return [((a0, a1), (k0, k1), (b0, m), (n0, n1)), ((a0, a1), (k0, k1), (m, b1), (n0, n1))]
    m = (n0 + n1) / 2; return [((a0, a1), (k0, k1), (b0, b1), (n0, m)), ((a0, a1), (k0, k1), (b0, b1), (m, n1))]
def rec(box, depth):
    stats["nodes"] += 1
    if empty(box): stats["empty"] += 1; return
    if find_leaf(box): stats["leaf"] += 1; return
    if depth > 26 or stats["nodes"] > NODEMAX:
        stats["fail"] += 1; fails.append(box); return
    sp = split(box)
    if sp is None: stats["fail"] += 1; fails.append(box); return
    for b in sp: rec(b, depth + 1)
A1 = F(sys.argv[1]) if len(sys.argv) > 1 else F(1, 25)
NODEMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
rec(((A1, F(2, 5)), (F(0), F(1, 2)), (F(0), INF), (F(1), INF)), 0)
print(f"alpha >= {A1}: {stats}")
for b in fails[:15]: print("  fail box", [(float(x), None if y is None else float(y)) for x, y in b])
