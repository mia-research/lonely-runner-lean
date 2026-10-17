#!/usr/bin/env python3
"""Exact (Fractions) 3/28 box tree over ratios x_i = v_i/v5 on the root box x_i in [X1, 1] (i = 1..4), with sevenths
splitting, serialised for Lean.  Leaf (L num den n1 n2 n3 n4 n5): window [L, L + K] in time units 1/v5 with
a_i L >= n_i + 1/7, b_i (L + K) <= n_i + 6/7 (runner 5: ratio 1).  E: empty box (a_i >= b_{i+1} or a_4 >= 1).
S d l r: split coordinate d (0..3) at the point m(box, d) (a sevenths point inside the box nearest the midpoint, else the
midpoint).  Usage: o7_kbox_exact_v2.py X1num X1den out.txt"""
import sys, time
from fractions import Fraction as Fr
sys.setrecursionlimit(100000)
K = Fr(3, 28); S7, S67 = Fr(1, 7), Fr(6, 7)
def runner_L(a, b, T=Fr(200)):
    out = []; n = 0
    while True:
        lo = (n + S7) / a; hi = (n + S67) / b - K
        if lo > T: break
        if hi >= lo: out.append((lo, hi, n))
        n += 1
    return out
def leaf(box):
    cur = [(lo, hi, (n,)) for lo, hi, n in runner_L(Fr(1), Fr(1))]
    for i in (3, 2, 1, 0):
        B = runner_L(*box[i]); nxt = []; p = q = 0
        while p < len(cur) and q < len(B):
            lo, hi = max(cur[p][0], B[q][0]), min(cur[p][1], B[q][1])
            if hi >= lo: nxt.append((lo, hi, (B[q][2],) + cur[p][2]))
            if cur[p][1] < B[q][1]: p += 1
            else: q += 1
        cur = nxt
        if not cur: return None
    L, _, ns = cur[0]
    return L, ns          # ns = (n1, n2, n3, n4, n5)
def split_pt(a, b):
    m = (a + b) / 2
    ks = [Fr(k, 7) for k in range(1, 7) if a < Fr(k, 7) < b]
    return min(ks, key=lambda z: abs(z - m)) if ks else m
cnt = {"L": 0, "E": 0, "S": 0}
def build(box, depth=0):
    if any(box[i][0] >= box[i + 1][1] for i in range(3)) or box[3][0] >= 1:
        cnt["E"] += 1; return "E"
    r = leaf(box)
    if r is not None:
        cnt["L"] += 1; L, ns = r
        return f"(L {L.numerator} {L.denominator} {' '.join(map(str, ns))})"
    w = [b - a for a, b in box]; d = max(range(4), key=lambda k: w[k])
    if w[d] < Fr(1, 4000): raise RuntimeError(f"stuck at {box}")
    m = split_pt(*box[d]); cnt["S"] += 1
    l = list(box); l[d] = (box[d][0], m); r_ = list(box); r_[d] = (m, box[d][1])
    return f"(S {d} {build(l, depth + 1)} {build(r_, depth + 1)})"
if __name__ == "__main__":
    X1 = Fr(int(sys.argv[1]), int(sys.argv[2])); t0 = time.time()
    tree = build([(X1, Fr(1))] * 4)
    open(sys.argv[3], "w").write(tree + "\n")
    print(f"root x_i in [{X1}, 1]: leaves {cnt['L']}, empty {cnt['E']}, splits {cnt['S']}, {len(tree)} chars, "
          f"{time.time() - t0:.0f} s")
