#!/usr/bin/env python3
"""Exact leaf data, §5 k = 1, alpha <= 1/50 (v2). As s5k1_small_gen_v1 with lam on a grid of 1/20:
(A) runner-4 leaves on (1, 25/14], [16/5, 8], [20, 45/2];  (B) strip leaves with mu0 = 1064/5000 on [25/14, 16/5];
(S) the (lam, lam5) tree on [25/14, 16/5] x [lam, 30] (ivt_box leaves, term-wise bounds, P-intervals >= 1/50);
(R5) one 4-runner ivt_box interval of length >= 1/(30 - 16/5) + 2/90 over the whole strip.
Writes s5k1_small_leaves_v1.lean.txt (Lean data) and prints counts."""
import math
from fractions import Fraction as F
W = F(1, 50); MU0 = F(1064, 5000)
def gridify(x): return F(math.floor(x * 20), 20)
def greedy(lo, hi, leaf_for):
    out = []; l0 = lo
    while l0 < hi:
        l1 = hi; best = None
        while l1 > l0:
            lf = leaf_for(l0, l1)
            if lf: best = (l1, lf); break
            nl = gridify(l1 - F(1, 40))
            l1 = nl if nl > l0 else (l0 + l1) / 2
            if l1 - l0 < F(1, 4000): break
        if not best: raise SystemExit(f"stuck at {float(l0)}")
        out.append((l0, best[0]) + best[1]); l0 = best[0]
    return out
def leafA(l0, l1):
    for m in range(0, 12):
        pa = max(F(1, 6), (F(m) - F(1, 3)) / (l0 - 1)) if l0 > 1 else F(1, 6)
        pb = pa + W
        if pb <= F(1, 3) and (F(m) - F(1, 3)) <= (l0 - 1) * pa and l1 * pb <= F(m) + F(1, 3): return (m, pa, pb)
    return None
def leafB(l0, l1):
    for m in range(0, 6):
        pa = max(F(1, 6), (F(m) - F(2, 3) + MU0) / (l0 - 1))
        pb = pa + W
        if pb <= F(2, 3) - MU0 and l1 * pb <= F(m) + F(2, 3) - MU0 and F(m) - F(2, 3) + MU0 <= (l0 - 1) * pa: return (m, pa, pb)
    return None
A = greedy(F(1), F(25, 14), leafA) + greedy(F(16, 5), F(8), leafA) + greedy(F(20), F(45, 2), leafA)
B = greedy(F(25, 14), F(16, 5), leafB)
print("A:", len(A), [(float(a), float(b), m) for a, b, m, pa, pb in A])
print("B:", len(B), [(float(a), float(b), m) for a, b, m, pa, pb in B])
# (S) tree with term-wise bounds
def pair_ok(c, a, b, e, pa, pb, lb, kb):
    """c + a P + b lam P + e lam5 P >= 0 for P in [pa, pb], lam in lb, lam5 in kb, each term at its worst corner (P >= 0)"""
    t = c + min(a * pa, a * pb)
    t += min(b * l * P for l in lb for P in (pa, pb)) if b else 0
    t += min(e * k * P for k in kb for P in (pa, pb)) if e else 0
    return t >= 0
def leafS_ok(n1, m3, m4, m5, pa, pb, lb, kb):
    if not (n1 + F(1, 6) <= pa and pb <= n1 + F(5, 6) and pb - pa >= W): return False
    # bounds as (const, coefP, coef lamP, coef lam5P)
    lows = [(F(1, 6), 0, 0, 0), (m3 + F(1, 6), -1, 0, 0), (m4 + F(1, 6), 0, -1, 0), (m5 + F(1, 6), 0, 0, -1)]
    ups = [(F(5, 6), 0, 0, 0), (m3 + F(5, 6), -1, 0, 0), (m4 + F(5, 6), 0, -1, 0), (m5 + F(5, 6), 0, 0, -1)]
    for u in ups:
        for l in lows:
            if not pair_ok(u[0] - l[0], u[1] - l[1], u[2] - l[2], u[3] - l[3], pa, pb, lb, kb): return False
    return True
def findS(lb, kb, four=False):
    lc = (lb[0] + lb[1]) / 2; kc = (kb[0] + kb[1]) / 2 if kb else None
    width = W if not four else F(1, 1) / (30 - F(16, 5)) + F(2, 90)
    for n1 in range(2):
        pa = n1 + F(1, 6)
        while pa + width <= n1 + F(5, 6):
            pb = pa + width; P = (pa + pb) / 2
            for yi in range(20, 101):
                y = F(yi, 120)
                m3 = math.floor(y + P - F(1, 6)); m4 = math.floor(y + lc * P - F(1, 6))
                if four:
                    if leafS_ok(n1, m3, m4, 0, pa, pb, lb, (F(0), F(0))) or True:
                        # 4-runner: drop runner 5 by checking with lam5 bounds collapsing its constraints: emulate with
                        # m5 huge-free check -> use dedicated check below
                        pass
                    if leaf4_ok(n1, m3, m4, pa, pb, lb): return (n1, m3, m4, 0, pa, pb)
                else:
                    m5 = math.floor(y + kc * P - F(1, 6))
                    if leafS_ok(n1, m3, m4, m5, pa, pb, lb, kb): return (n1, m3, m4, m5, pa, pb)
            pa += width / 8
    return None
def leaf4_ok(n1, m3, m4, pa, pb, lb):
    if not (n1 + F(1, 6) <= pa and pb <= n1 + F(5, 6)): return False
    lows = [(F(1, 6), 0, 0), (m3 + F(1, 6), -1, 0), (m4 + F(1, 6), 0, -1)]
    ups = [(F(5, 6), 0, 0), (m3 + F(5, 6), -1, 0), (m4 + F(5, 6), 0, -1)]
    for u in ups:
        for l in lows:
            if not pair_ok(u[0] - l[0], u[1] - l[1], u[2] - l[2], 0, pa, pb, lb, None): return False
    return True
nodes = 0
def build(lb, kb, depth):
    global nodes; nodes += 1
    if kb[1] < lb[0]: return "E"
    lf = findS(lb, kb)
    if lf:
        n1, m3, m4, m5, pa, pb = lf
        return f"(L {n1} {m3} {m4} {m5} ({pa.numerator}/{pa.denominator}) ({pb.numerator}/{pb.denominator}))"
    if depth > 24: raise SystemExit(f"fail {lb} {kb}")
    if (lb[1] - lb[0]) * 8 >= (kb[1] - kb[0]):
        m = (lb[0] + lb[1]) / 2; return f"(S 0 {build((lb[0], m), kb, depth + 1)} {build((m, lb[1]), kb, depth + 1)})"
    m = (kb[0] + kb[1]) / 2; return f"(S 1 {build(lb, (kb[0], m), depth + 1)} {build(lb, (m, kb[1]), depth + 1)})"
treeS = build((F(25, 14), F(16, 5)), (F(25, 14), F(30)), 0)
print("S tree nodes", nodes, "leaves", treeS.count("(L "), "chars", len(treeS))
R5 = findS((F(25, 14), F(16, 5)), None, four=True)
print("R5 leaf:", R5)
open("s5k1_small_treeS_v1.lean.txt", "w").write(treeS)
import pickle; pickle.dump((A, B, R5), open("s5k1_small_gen_v2.pkl", "wb"))
