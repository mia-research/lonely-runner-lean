"""Case B as order six on the cluster plus a fast pair?

mirror_overlap_v1: on the mirror lattice the top pair never drives the cascade; the middle
disparities do, and in the small examples the cluster sits at its first reading while the top pair
reads near 1/2.  Hypothesis H(r): for every hard set, some t has the r smallest disparities clear
at 1/6 (order six's threshold, proved for any five) and the remaining ones clear at 1/8.

Exact test.  With a threshold th_d per disparity the closed-condition argument of Theorem 9 holds
unchanged: a feasible t exists iff some opening (N + th_d)/d, 0 <= N < d, is feasible (the latest
opening before a feasible t is feasible).  Integer speeds: period 1, so N < d suffices.
Reported for r = 5 (cluster of five, top pair at 1/8), r = 4 (cluster of four at 1/6), and the
control r = 7 (all at 1/6: order-eight sets need not be lonely at 1/6).
"""
import json, os
from fractions import Fraction as F
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]

def clear(d, t, th):
    x = (d * t) % 1
    return th <= x <= 1 - th

def feasible(S, ths):
    for d, th in zip(S, ths):
        for N in range(d):
            t = (N + th) / d
            if all(clear(e, t, u) for e, u in zip(S, ths)): return t
    return None

for r in (5, 4, 6, 7):
    c = Counter(); fails = []
    for S in H:
        srt = sorted(S)
        ths = [F(1, 6)] * r + [F(1, 8)] * (7 - r)
        t = feasible(srt, ths)
        c[t is not None] += 1
        if t is None and len(fails) < 6: fails.append(S)
    print(f"r = {r}: the {r} smallest at 1/6, the rest at 1/8: holds on {c[True]} of {len(H)} hard sets; fails e.g. {fails}")
