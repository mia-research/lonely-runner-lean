#!/usr/bin/env python3
"""v3 (order: folds, boxes, windows): F4 laps (0,0,0,0), (0,0,0,1), (0,1,1,2) and boxes (0,0,0,1,3), (0,1,1,2,3) added (E90).
Builds the §8 certificate tree with exactly the semantics of S8CertCore_v1.lean (clip at every node, checks at the
clipped cell, splits recorded as (dimension, mid)), verifies it in Python with that semantics, and writes the tree as
Lean data (S8CertData_v1.lean). Root cell: ratios x2, x3 in [1,3], x4 in [1,6], x5 in [1, inf) (hi 3 = 0)."""
import sys
from fractions import Fraction as F
sys.setrecursionlimit(100000)
W3 = [(0,0,0),(1,2,3),(0,1,1),(0,0,1),(0,1,2),(2,6,7),(1,3,4)]
F4 = [(0,0,0,0),(0,0,0,1),(0,1,1,2)]
BX = [(0,0,0,0,0),(0,0,0,0,1),(0,0,0,1,1),(0,0,1,1,2),(0,1,2,3,4),(0,0,0,1,2),(0,1,2,3,8),(1,3,4,5,7),(1,2,3,4,6),
      (0,1,1,2,2),(1,3,4,6,8),(0,1,2,3,9),(2,6,7,10,14),(1,3,4,6,17),(1,3,4,6,18),(0,1,1,2,6),(0,0,0,1,3),(0,1,1,2,3)]
def clip(c):
    lo, hi = c
    a2 = max(lo[0], F(1)); a3 = max(lo[1], a2); a4 = max(lo[2], a3); a5 = max(lo[3], a4)
    b4 = hi[2] if hi[3] == 0 else min(hi[2], hi[3]); b3 = min(min(hi[1], F(3)), b4); b2 = min(hi[0], b3)
    return ((a2, a3, a4, a5), (b2, b3, b4, hi[3]))
def bounded3(c): return all(c[1][i] > 0 for i in range(3))
def emptyB(c):
    lo, hi = c
    return hi[0] < lo[0] or hi[1] < lo[1] or hi[2] < lo[2] or (hi[3] != 0 and hi[3] < lo[3])
def LO(c, j): return F(1) if j == 0 else c[0][j - 1]
def HI(c, j): return F(1) if j == 0 else c[1][j - 1]
def bandOK(c, m, L, U):
    return all(LO(c, i) > 0 and HI(c, i) > 0 and F(6 * m[i] + 1, 6) <= LO(c, i) * L and HI(c, i) * U <= F(6 * m[i] + 5, 6)
               for i in range(len(m)))
def LU(c, m):
    if any(HI(c, i) <= 0 for i in range(len(m))): return None
    return max(F(6 * m[i] + 1, 6) / LO(c, i) for i in range(len(m))), min(F(6 * m[i] + 5, 6) / HI(c, i) for i in range(len(m)))
def w3OK(c, m, L, U):
    l = U - L; a = c[0][2]; b = c[0][3]; h3 = c[1][3]
    if not (bandOK(c, m, L, U) and L >= 0 and a > 0 and a <= b): return False
    if h3 == 0: return F(1) / (3 * a) + F(2) / (3 * b) <= l
    return (F(1) / (3 * a) + F(1) / (3 * b) <= l and a + h3 <= 3 * 64 * a and
            all(not (3 * mm * a < a + h3) or (mm + F(1, 3)) / b <= l for mm in range(64)))
def f4OK(c, m, L, U): return bandOK(c, m, L, U) and L >= 0 and c[0][3] > 0 and F(1, 3) <= c[0][3] * (U - L)
def boxOK(c, k):
    return c[1][3] != 0 and all(LO(c, i) > 0 and HI(c, j) > 0 and (6 * k[i] + 1) * HI(c, j) <= (6 * k[j] + 5) * LO(c, i)
                                for i in range(5) for j in range(5))
def certify(c):
    for m in F4:
        r = LU(c, m)
        if r and f4OK(c, m, *r): return ("f4", m, r)
    for k in BX:
        if boxOK(c, k): return ("box", k, None)
    for m in W3:
        r = LU(c, m)
        if r and w3OK(c, m, *r): return ("w3", m, r)
    return None
def setHi(c, d, x): hi = list(c[1]); hi[d] = x; return (c[0], tuple(hi))
def setLo(c, d, x): lo = list(c[0]); lo[d] = x; return (tuple(lo), c[1])
stats = {"leaf": 0, "none": 0, "node": 0, "maxd": 0}
def build(c, depth):
    stats["maxd"] = max(stats["maxd"], depth)
    assert bounded3(c)
    cc = clip(c); assert bounded3(cc)
    if emptyB(cc): stats["none"] += 1; return ("none",)
    r = certify(cc)
    if r: stats["leaf"] += 1; return ("leaf", r)
    if depth > 60: raise SystemExit(f"FAIL at {cc}")
    lo, hi = cc
    d = mid = None
    for i in range(4):
        if hi[i] == 0:
            if lo[i] < 30: d, mid = i, F(30); break
        elif hi[i] - lo[i] > 1:
            d, mid = i, F(int(lo[i]) + 1); break
    if d is None:
        widths = [(hi[i] - lo[i]) if hi[i] != 0 else F(-1) for i in range(4)]
        d = max(range(4), key=lambda j: widths[j]); mid = (lo[d] + hi[d]) / 2
        if widths[d] <= 0: raise SystemExit(f"FAIL unsplittable {cc}")
    stats["node"] += 1
    return ("node", d, mid, build(setHi(cc, d, mid), depth + 1), build(setLo(cc, d, mid), depth + 1))
root = ((F(1), F(1), F(1), F(1)), (F(3), F(3), F(6), F(0)))
tree = build(root, 0)
print("tree:", stats)
def q(x): return f"({x.numerator}/{x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"
def vec(xs): return "![" + ", ".join(str(x) for x in xs) + "]"
lines = []
def emit(t):
    if t[0] == "none": return "Tree.none"
    if t[0] == "leaf":
        kind, m, r = t[1]
        if kind == "box": return f"(Tree.leaf (Stmt.box {vec(m)}))"
        return f"(Tree.leaf (Stmt.{kind} {vec(m)} {q(r[0])} {q(r[1])}))"
    return f"(Tree.node {t[1]} {q(t[2])}\n {emit(t[3])}\n {emit(t[4])})"
body = emit(tree)
open("S8CertTree_v3.txt", "w").write(body)
print("Lean term characters:", len(body))
