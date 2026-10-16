#!/usr/bin/env python3
"""Certificate for the lam = +-1 cases (§6, D >= 15, gcd(v1, D) = 1, near-runner). Parameters: u = (c+1)/c,
q4 = v4/v3 in [1, 4/(5-u)], mu = v4/(3 v5) in [0, 1/3]. With p = runner 1's phase j/D and p4 = lam p (mod 1), the
after-window conditions (s6_window_fold) are
   p in [1/6, 5/9],  lam p + 5 q4/6 - mu >= m + 1/6,  lam p + q4 u/6 + mu <= m + 5/6,
the before-window ones (s6_window_fold_before, phase 1 - p4)
   p in [4/9, 5/6],  1 - lam p + 5 q4/6 - mu >= m + 1/6,  1 - lam p + q4 u/6 + mu <= m + 5/6,
and the sum lemma (lam = 1, c <= 2, where delta = v1, r1 = q4 - 1):  p in [1/3 + mu/q4, (5/6)(2 - q4)].
A cell is certified by (kind, m, a) when every p in [a, a + L] satisfies its conditions at every parameter of the cell
(worst corners; the q4 upper bound is min(q4_hi, 4/(5 - u_hi))). Roots: A: u in [1, 4/3] (c >= 3), L = 1/15;
B: u = 3/2 (c = 2) and C: u = 2 (c = 1), L = 1/18 (then D >= 18; D = 15..17 separately).
Writes the trees and reports sizes."""
import sys, json
from fractions import Fraction as F
sys.setrecursionlimit(100000)
def feasible(cell, lam, kind, m, L, allow_sum):
    (ul, uh), (ql, qh), (ml, mh) = cell
    qh = min(qh, F(4) / (5 - uh))
    if qh < ql: return F(0)        # empty cell: any a works
    lo, hi = None, None
    if kind == "after":
        lo, hi = F(1, 6), F(5, 9) - L
        if lam == 1:
            lo = max(lo, m + F(1, 6) - F(5, 6) * ql + mh)
            hi = min(hi, m + F(5, 6) - L - qh * uh / 6 - mh)
        else:  # -p: lower worst at p = a + L, upper worst at p = a
            hi = min(hi, -(m + F(1, 6) - F(5, 6) * ql + mh) - L)
            lo = max(lo, -(m + F(5, 6) - qh * uh / 6 - mh))
    elif kind == "before":
        lo, hi = F(4, 9), F(5, 6) - L
        if lam == 1:   # 1 - p: lower worst at p = a + L, upper worst at p = a
            hi = min(hi, 1 - (m + F(1, 6) - F(5, 6) * ql + mh) - L)
            lo = max(lo, 1 - (m + F(5, 6) - qh * uh / 6 - mh))
        else:          # 1 + p
            lo = max(lo, m + F(1, 6) - F(5, 6) * ql + mh - 1)
            hi = min(hi, m + F(5, 6) - qh * uh / 6 - mh - 1 - L)
    else:  # sum
        if not (allow_sum and lam == 1): return None
        lo = F(1, 3) + mh / ql
        hi = F(5, 6) * (2 - qh) - L
    return lo if lo <= hi else None
def certify(cell, lam, L, allow_sum):
    for kind in ("after", "before", "sum"):
        for m in range(-2, 3):
            a = feasible(cell, lam, kind, m, L, allow_sum)
            if a is not None: return (kind, m, a)
    return None
def build(cell, lam, L, allow_sum, depth, stats):
    r = certify(cell, lam, L, allow_sum)
    if r: stats["leaf"] += 1; return ("leaf", r)
    if depth > 40: raise SystemExit(f"FAIL lam={lam} cell={cell}")
    widths = [cell[i][1] - cell[i][0] for i in range(3)]
    d = max(range(3), key=lambda i: widths[i])
    if widths[d] == 0: raise SystemExit(f"FAIL degenerate {cell}")
    a, b = cell[d]; mid = (a + b) / 2
    stats["node"] += 1
    c1 = list(cell); c1[d] = (a, mid); c2 = list(cell); c2[d] = (mid, b)
    return ("node", d, mid, build(tuple(c1), lam, L, allow_sum, depth + 1, stats), build(tuple(c2), lam, L, allow_sum, depth + 1, stats))
roots = {"A": (((F(1), F(4, 3)), (F(1), F(12, 11)), (F(0), F(1, 3))), F(1, 15), False),
         "B": (((F(3, 2), F(3, 2)), (F(1), F(8, 7)), (F(0), F(1, 3))), F(1, 18), True),
         "C": (((F(2), F(2)), (F(1), F(4, 3)), (F(0), F(1, 3))), F(1, 18), True)}
trees = {}
for lam in (1, -1):
    for name, (cell, L, allow) in roots.items():
        stats = {"leaf": 0, "node": 0}
        trees[(lam, name)] = build(cell, lam, L, allow, 0, stats)
        print(f"lam {lam:+d}, root {name} (L = {L}): {stats}")
import pickle; pickle.dump(trees, open("s6_lam_cert_v1.pkl", "wb"))
