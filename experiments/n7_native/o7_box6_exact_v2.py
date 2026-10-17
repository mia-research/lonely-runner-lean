#!/usr/bin/env python3
"""Exact six-runner box tree (as o7_box6_v1) serialised for Lean (`LRC.O7Box6`).  Root: x1..x4 in [X, 1], x5 in [Y, 1].
Leaf (L p q n0 n1 n2 n3 n4 n5): instant tau = p/q, laps for x1..x5 and runner 6.  Split rule: k/42 nearest midpoint
(first k on ties), else midpoint.  Usage: o7_box6_exact_v2.py Xn Xd Yn Yd T out.txt"""
import sys, time
from fractions import Fraction as Fr
sys.setrecursionlimit(100000)
S7, S67 = Fr(1, 7), Fr(6, 7)
def runner_tau(a, b, T):
    out = []; n = 0
    while True:
        lo = (n + S7) / a; hi = (n + S67) / b
        if lo > T: break
        if hi >= lo: out.append((lo, min(hi, T), n))
        n += 1
    return out
def leaf(box, T):
    cur = [(lo, hi, (n,)) for lo, hi, n in runner_tau(Fr(1), Fr(1), T)]
    for i in (4, 3, 2, 1, 0):
        B = runner_tau(*box[i], T); nxt = []; p = q = 0
        while p < len(cur) and q < len(B):
            lo, hi = max(cur[p][0], B[q][0]), min(cur[p][1], B[q][1])
            if hi >= lo: nxt.append((lo, hi, (B[q][2],) + cur[p][2]))
            if cur[p][1] < B[q][1]: p += 1
            else: q += 1
        cur = nxt
        if not cur: return None
    return cur[0][0], cur[0][2]
def split_pt(a, b):
    m = (a + b) / 2
    ks = [Fr(k, 42) for k in range(1, 42) if a < Fr(k, 42) < b]
    best = ks[0] if ks else m
    for z in ks:
        if abs(z - m) < abs(best - m): best = z
    return best
cnt = {"L": 0, "E": 0}
def build(box, T):
    if any(box[i][0] >= box[i + 1][1] for i in range(4)) or box[4][0] >= 1:
        cnt["E"] += 1; return "E"
    r = leaf(box, T)
    if r is not None:
        cnt["L"] += 1; tau, ns = r
        return f"(L {tau.numerator} {tau.denominator} {' '.join(map(str, ns))})"
    w = [b - a for a, b in box]; d = max(range(5), key=lambda k: w[k])
    if w[d] < Fr(1, 20000): raise RuntimeError(f"stuck {box}")
    m = split_pt(*box[d])
    l = list(box); l[d] = (box[d][0], m); r_ = list(box); r_[d] = (m, box[d][1])
    return f"(S {d} {build(l, T)} {build(r_, T)})"
if __name__ == "__main__":
    X = Fr(int(sys.argv[1]), int(sys.argv[2])); Y = Fr(int(sys.argv[3]), int(sys.argv[4])); T = Fr(int(sys.argv[5]))
    t0 = time.time()
    tree = build([(X, Fr(1))] * 4 + [(max(X, Y), Fr(1))], T)
    open(sys.argv[6], "w").write(tree + "\n")
    print(f"six-runner tree x1..x4 in [{X}, 1], x5 in [{max(X, Y)}, 1]: leaves {cnt['L']}, empty {cnt['E']}, "
          f"{len(tree)} chars, {time.time() - t0:.0f} s")
