#!/usr/bin/env python3
"""Observation only. Owner: global isolation has multiple instances and deformation (residue) opportunities - count
those, not one flank's openings. Opportunities: the unit-grid instants c/q, 0 < c < q, gcd(c, q) = 1, for q = 2, 3, ...
(q = 6 is the order-6 ideal's own pair 1/6, 5/6; every lonely instant is one of these, E66). At c/q runner d reads
(d c mod q)/q and blocks iff that reading is outside [1/6, 5/6].
Per set: q* = least q with a lonely unit instant; opportunities before it (sum of phi(q), q < q*), all blocked; at each
blocked opportunity, how many runners block it (multiplicity); share of each runner's blocks; comparison of q* with the
cascade instant's denominator."""
from fractions import Fraction as F
from collections import Counter
from math import gcd
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def T(S):
    t = F(1, 6 * S[0])
    while True:
        b = [d for d in S if cd(d * t) < F(1, 6)]
        if not b: return t
        t = max(F(6 * round(d * t) + 1, 6 * d) for d in b)
def blocks(d, c, q): r = (d * c) % q; return 6 * r < q or 6 * r > 5 * q
qstar = Counter(); opp = Counter(); mult = Counter(); per_runner_frac = Counter(); same = Counter(); nlonely = Counter()
for S in rows:
    q = 2; tot = 0; m_here = Counter()
    while True:
        units = [c for c in range(1, q) if gcd(c, q) == 1]
        lon = [c for c in units if not any(blocks(d, c, q) for d in S)]
        if lon: break
        for c in units: m_here[sum(blocks(d, c, q) for d in S)] += 1
        tot += len(units); q += 1
    qstar[q] += 1; nlonely[len(lon)] += 1; mult.update(m_here)
    opp[(tot // 10) * 10] += 1
    same[q == T(S).denominator] += 1
print(f"sets {len(rows)}")
print("q* (least grid with a lonely unit instant):", sorted(qstar.items())[:30])
print("lonely unit instants at q*:", dict(sorted(nlonely.items())))
print("blocked opportunities before q* (binned by 10):", sorted(opp.items())[:20])
print("how many runners block each blocked opportunity (multiplicity):", dict(sorted(mult.items())))
print("q* equals the cascade instant's denominator:", dict(same))
