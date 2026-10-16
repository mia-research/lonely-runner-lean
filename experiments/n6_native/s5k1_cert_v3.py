#!/usr/bin/env python3
"""Exact generator of the §5 k >= 2 large-alpha certificate tree (alpha >= 1/25), matching the Lean checker
S5Large_v1.lean. Box = (a0, a1, k0, k1, b0, b1|None, n0, n1|None). Speeds / v2:
  lo = [a0, 1, 1 + a0 k0, 1 + b0, (1 + b0) n0],  hi = [a1, 1, 1 + a1 k1, 1 + b1, (1 + b1) n1]  (None if unbounded).
Leaf (kind, laps m[0..4]): kind 0 = box (all five in bands), kind r in 1..4 = runner r folded (0-based index r; others in
bands), kind 5 = window_two (runners 0, 1, 2 in bands; runners 3, 4 by window_two). Window:
  ya = max over the block of (m_i + 1/6)/lo_i,  yb = min over the block of (m_i + 5/6)/hi_i  (hi_i must be finite)
  ok iff ya <= yb and: kind r: lo_r (yb - ya) >= 1/3;  kind 5: lo_3 (yb - ya) >= 2/3.
Split (dim, point): dim 0..3 = alpha, kappa, beta, nu; point = midpoint, or for an unbounded beta: max(1, 2 b0), for an
unbounded nu: max(2, 2 n0). Empty: a0 (3 - k1) >= 1, or b1 <= a0 k0.
Writes the Lean tree to s5_cert_tree_v1.lean.txt and prints stats.
k = 1 version (s5k1_cert_v3): kappa fixed at 1, non-strict windows, leaf kinds 6 / 7 = box inside the tight
neighbourhood N1 of (1,3,4,5,9) / N2 of (1,2,3,4,5) (tight_13459, tight_12345)."""
import math, sys
from fractions import Fraction as F
sys.setrecursionlimit(10000)
NMAX1 = 8
def bounds(B):
    a0, a1, k0, k1, b0, b1, n0, n1 = B
    lo = [a0, F(1), 1 + a0 * k0, 1 + b0, (1 + b0) * n0]
    hi = [a1, F(1), 1 + a1 * k1, None if b1 is None else 1 + b1, None if (b1 is None or n1 is None) else (1 + b1) * n1]
    return lo, hi
def window(B, kind, m):
    lo, hi = bounds(B)
    blk = [0, 1, 2, 3, 4] if kind == 0 else ([0, 1, 2] if kind == 5 else [i for i in range(5) if i != kind])
    ya = max((m[i] + F(1, 6)) / lo[i] for i in blk)
    if any(hi[i] is None for i in blk): return None
    yb = min((m[i] + F(5, 6)) / hi[i] for i in blk)
    return ya, yb
def ok(B, kind, m):
    w = window(B, kind, m)
    if w is None: return False
    ya, yb = w
    if ya > yb: return False
    lo, _ = bounds(B)
    if kind == 0: return True
    if kind == 5: return lo[3] * (yb - ya) >= F(2, 3)
    return lo[kind] * (yb - ya) >= F(1, 3)
def laps(L, U, lo, hi):
    a, b = max(0, math.floor(L * lo) - 1), math.floor(U * hi) + 2
    return range(a, min(b, a + 40))
def tp(B):
    a0, a1, k0, k1, b0, b1, n0, n1 = B
    if b1 is None or n1 is None: return None
    if 14 * a1 <= 5 and 5 <= 17 * a0 and 5 * (1 + b1) <= 29 * a0 and 43 * a1 <= 5 * (1 + b0) * n0 and 5 * (1 + b1) * n1 <= 47 * a0:
        return (6, (0, 0, 0, 0, 0))
    if 5 <= 11 * a0 and 19 * a1 <= 5 * (1 + b0) and 5 * (1 + b1) <= 23 * a0 and 5 * (1 + b1) * n1 <= 29 * a0:
        return (7, (0, 0, 0, 0, 0))
    return None
def find(B):
    t = tp(B)
    if t: return t
    lo, hi = bounds(B)
    def ext(order, L, U, m):
        if not order: yield L, U, m; return
        i = order[0]
        if hi[i] is None: return
        for mm in laps(L, U, lo[i], hi[i]):
            a = max(L, (mm + F(1, 6)) / lo[i]); b = min(U, (mm + F(5, 6)) / hi[i])
            if a <= b:
                m2 = dict(m); m2[i] = mm
                yield from ext(order[1:], a, b, m2)
    def lap5(m): return tuple(m.get(i, 0) for i in range(5))
    for n1 in range(NMAX1):
        L, U = (n1 + F(1, 6)) / lo[0], (n1 + F(5, 6)) / hi[0]
        if L > U: continue
        for L3, U3, m in ext([2, 1], L, U, {0: n1}):
            if ok(B, 5, lap5(m)): return (5, lap5(m))
            for a, b, mm in ext([3], L3, U3, m):
                if ok(B, 4, lap5(mm)): return (4, lap5(mm))
            for a, b, mm in ext([4], L3, U3, m):
                if ok(B, 3, lap5(mm)): return (3, lap5(mm))
        for a, b, m in ext([2, 1, 3, 4], L, U, {0: n1}):
            if ok(B, 0, lap5(m)): return (0, lap5(m))
        for order, r in (([1, 3, 4], 2), ([2, 3, 4], 1)):
            for a, b, m in ext(order, L, U, {0: n1}):
                if ok(B, r, lap5(m)): return (r, lap5(m))
    return None
def empty(B):
    a0, a1, k0, k1, b0, b1, n0, n1 = B
    return a0 * (3 - k1) >= 1 or (b1 is not None and b1 <= a0 * k0)
def split(B, d):
    a0, a1, k0, k1, b0, b1, n0, n1 = B
    if d == 0: m = (a0 + a1) / 2; return (a0, m, k0, k1, b0, b1, n0, n1), (m, a1, k0, k1, b0, b1, n0, n1)
    if d == 1: raise ValueError('no kappa split for k = 1')
    if d == 1: m = (k0 + k1) / 2; return (a0, a1, k0, m, b0, b1, n0, n1), (a0, a1, m, k1, b0, b1, n0, n1)
    if d == 2:
        m = max(F(1), 2 * b0) if b1 is None else (b0 + b1) / 2
        return (a0, a1, k0, k1, b0, m, n0, n1), (a0, a1, k0, k1, m, b1, n0, n1)
    m = max(F(2), 2 * n0) if n1 is None else (n0 + n1) / 2
    return (a0, a1, k0, k1, b0, b1, n0, m), (a0, a1, k0, k1, b0, b1, m, n1)
def choose(B):
    a0, a1, k0, k1, b0, b1, n0, n1 = B
    wa = (a1 - a0) / a1 * 4; wk = (k1 - k0) * 2
    wk = 0
    if b1 is None:
        if b0 >= 1 and wa > F(1, 50): return 0
        return 2
    wb = (b1 - b0) / (1 + b1) * 3
    if n1 is None:
        if max(wa, wb) > F(1, 50) and n0 >= 2: return 0 if wa >= wb else 2
        return 3
    wn = (n1 - n0) / n1 * 2
    ws = [wa, -1, wb, wn]; return ws.index(max(ws))
st = {"leaf": 0, "empty": 0, "split": 0, "fail": 0}
def build(B, depth):
    if empty(B): st["empty"] += 1; return "E"
    lf = find(B)
    if lf: st["leaf"] += 1; return f"(L {lf[0]} {lf[1][0]} {lf[1][1]} {lf[1][2]} {lf[1][3]} {lf[1][4]})"
    if depth > 46: st["fail"] += 1; return "FAIL"
    d = choose(B); l, r = split(B, d); st["split"] += 1
    return f"(S {d} {build(l, depth + 1)} {build(r, depth + 1)})"
# root, with forced alpha splits at the slab points of s5_cert_v2 (as successive dim-0 splits are midpoints, use the
# exact root [1/25, 2/5] and let the tree split)
root = (F(1, 25), F(1, 2), F(1), F(1), F(0), None, F(1), None)
t = build(root, 0)
print(st, "chars", len(t))
open("s5k1_cert_tree_v1.lean.txt", "w").write(t)
