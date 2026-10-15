#!/usr/bin/env python3
"""E42: the order-five scale change and shift, carried to order six. Order five (OrderFiveResidualN): instants on the
fastest runner F's lap points K/F, scaled (K -> mK, m a unit mod F), then shifted by k/5; multiples of 5 do not
move, F blocks only k = 0. Order six analogue: instants t = K/F + k/6, K in [0, F), k = 1..5 (enumerating all K
includes every scale change). For each residual set: is some such instant lonely; per runner, how many of the
five shifts k it blocks at the best K (budget: 5 shifts). Separately for the sets with no lonely opening at a
divisible flank (six_cells_budget_rest_v1)."""
from fractions import Fraction as F_
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
def clear(x):
    f = x - (x.numerator // x.denominator); return F_(1, 6) <= f <= F_(5, 6)
def clear_flank(d, e, j): r = d * (6 * j + 1) % (6 * e); return e <= r <= 5 * e
def lonely_at(S, b): return any(all(clear_flank(d, b, j) for d in S) for j in range(b))
res = Counter(); res_rest = Counter(); ex = []; fdiv = Counter()
for r in rows:
    S = eval(r[0]); Fm = max(S)
    hit = any(all(clear(F_(d * (6 * K + k * Fm), 6 * Fm)) for d in S) for K in range(Fm) for k in range(1, 6))
    res["some K/F + k/6 lonely" if hit else "none"] += 1
    fdiv["F multiple of 6" if Fm % 6 == 0 else "F not a multiple of 6"] += 1
    divs = [d for d in S if d % 6 == 0]
    if not any(lonely_at(S, e) for e in divs):
        res_rest["some K/F + k/6 lonely" if hit else "none"] += 1
        if not hit and len(ex) < 8: ex.append(S)
print("all residual sets:", dict(res), dict(fdiv))
print("sets with no divisible-flank opening:", dict(res_rest))
print("examples with neither:", ex)
