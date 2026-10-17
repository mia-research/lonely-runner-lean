#!/usr/bin/env python3
"""Small-separation tree (EXACT Fractions): ratios r = (v3, v4, v5, v6)/v2 in [1, R] (increasing).  Leaf: a stretch index
m in 0..M and a phase phi with v2 t = m + phi, phi in [1/7, 6/7] (runner 2 in band), and for every r in the box
r_k (m + phi) in band (term-wise: lo_k (m + phi) >= n_k + 1/7, hi_k (m + phi) <= n_k + 6/7).  Then for any v1 with
(M + 6/7)/v2 <= 6/(7 v1) and (m + 1/7)/v2 >= 1/(7 v1), i.e. v2 >= (7M + 6) v1 / 6, the instant lies in runner 1's first
stretch: first-stretch localisation for all such sets.  Split rule: the point k/42 nearest the midpoint, else midpoint.
Reports leaves, the stretch indices used, failures.  Usage: o7_sstree_v1.py R M"""
import sys, time
from fractions import Fraction as Fr
from collections import Counter
S7, S67 = Fr(1, 7), Fr(6, 7)
def leaf(box, M):
    for m in range(M + 1):
        cur = [(m + S7, m + S67)]                    # x = m + phi
        for lo, hi in box:
            B = []; n = int(lo * cur[0][0]) - 1
            while True:
                a, b = (n + S7) / lo, (n + S67) / hi
                if a > m + S67: break
                a, b = max(a, m + S7), min(b, m + S67)
                if b >= a: B.append((a, b))
                n += 1
            nxt = []
            for c0, c1 in cur:
                for a, b in B:
                    x0, x1 = max(c0, a), min(c1, b)
                    if x1 >= x0: nxt.append((x0, x1))
            cur = nxt
            if not cur: break
        if cur: return m
    return None
def split_pt(a, b):
    m = (a + b) / 2
    ks = [Fr(k, 42) for k in range(int(a * 42) + 1, int(b * 42) + 1) if a < Fr(k, 42) < b]
    best = ks[0] if ks else m
    for z in ks:
        if abs(z - m) < abs(best - m): best = z
    return best
def run(R, M):
    stack = [[(Fr(1), Fr(R))] * 4]; leaves = 0; empty = 0; fails = []; ms = Counter()
    while stack:
        box = stack.pop()
        if any(box[i][0] >= box[i + 1][1] for i in range(3)) or box[0][1] <= 1: empty += 1; continue
        m = leaf(box, M)
        if m is not None: leaves += 1; ms[m] += 1; continue
        w = [b - a for a, b in box]; d = max(range(4), key=lambda k: w[k])
        if w[d] < Fr(1, 4000): fails.append(box); continue
        x = split_pt(*box[d]); l = list(box); l[d] = (box[d][0], x); r = list(box); r[d] = (x, box[d][1])
        stack += [l, r]
    return leaves, empty, fails, ms
if __name__ == "__main__":
    R, M = int(sys.argv[1]), int(sys.argv[2]); t0 = time.time()
    leaves, empty, fails, ms = run(R, M)
    print(f"small-separation tree, r in [1, {R}]^4, stretches 0..{M}: leaves {leaves}, empty {empty}, failed {len(fails)}, "
          f"stretch indices {sorted(ms.items())}, {time.time() - t0:.0f} s")
    if fails:
        cl = Counter(tuple(round(float((a + b) / 2), 2) for a, b in f) for f in fails)
        print("   failure clusters:", cl.most_common(12))
