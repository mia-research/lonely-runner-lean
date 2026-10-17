#!/usr/bin/env python3
"""Six-runner box tree prototype (EXACT Fractions): ratios x_i = v_i/v6 (i = 1..5) in a root box, lonely-instant leaves.
Leaf: an instant tau (time in units 1/v6) and laps with a_i tau >= n_i + 1/7, b_i tau <= n_i + 6/7 for every
coordinate box [a_i, b_i], and runner 6 (ratio 1): n_6 + 1/7 <= tau <= n_6 + 6/7.  Empty boxes (no increasing point)
are dropped.  Splitting: at a point k/42 inside the interval nearest its midpoint (puts sixths and sevenths on faces),
else the midpoint.  Failures: boxes narrower than WMIN; reported by their centres.
Usage: o7_box6_v1.py X1num X1den X5num X5den T WMINden"""
import sys, time
from fractions import Fraction as Fr
from collections import Counter
sys.setrecursionlimit(100000)
S7, S67 = Fr(1, 7), Fr(6, 7)
def runner_tau(a, b, T):
    out = []; n = 0
    while True:
        lo = (n + S7) / a; hi = (n + S67) / b
        if lo > T: break
        if hi >= lo: out.append((lo, min(hi, T)))
        n += 1
    return out
def inter(A, B):
    i = j = 0; out = []
    while i < len(A) and j < len(B):
        lo, hi = max(A[i][0], B[j][0]), min(A[i][1], B[j][1])
        if hi >= lo: out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out
def leaf(box, T):
    cur = runner_tau(Fr(1), Fr(1), T)
    for i in (4, 3, 2, 1, 0):
        cur = inter(cur, runner_tau(*box[i], T))
        if not cur: return None
    return cur[0][0]
def split_pt(a, b):
    m = (a + b) / 2
    ks = [Fr(k, 42) for k in range(1, 42) if a < Fr(k, 42) < b]
    return min(ks, key=lambda z: abs(z - m)) if ks else m
def run(root, T, WMIN):
    stack = [root]; leaves = 0; empty = 0; fails = []
    while stack:
        box = stack.pop()
        if any(box[i][0] >= box[i + 1][1] for i in range(4)) or box[4][0] >= 1: empty += 1; continue
        if leaf(box, T) is not None: leaves += 1; continue
        w = [b - a for a, b in box]; d = max(range(5), key=lambda k: w[k])
        if w[d] < WMIN: fails.append(box); continue
        m = split_pt(*box[d])
        l = list(box); l[d] = (box[d][0], m); r = list(box); r[d] = (m, box[d][1])
        stack += [l, r]
    return leaves, empty, fails
if __name__ == "__main__":
    X1 = Fr(int(sys.argv[1]), int(sys.argv[2])); X5 = Fr(int(sys.argv[3]), int(sys.argv[4]))
    T = Fr(int(sys.argv[5])); WMIN = Fr(1, int(sys.argv[6])); t0 = time.time()
    root = [(X1, Fr(1))] * 4 + [(max(X1, X5), Fr(1))]
    leaves, empty, fails = run(root, T, WMIN)
    print(f"root x1..x4 in [{X1}, 1], x5 in [{max(X1, X5)}, 1], T = {T}, WMIN = {WMIN}: leaves {leaves}, empty {empty}, "
          f"failed {len(fails)}, {time.time() - t0:.0f} s")
    cl = Counter(tuple(round(float((a + b) / 2), 2) for a, b in f) for f in fails)
    print("   failure clusters (centres to 0.01):", cl.most_common(20))
