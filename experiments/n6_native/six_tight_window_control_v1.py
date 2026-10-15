#!/usr/bin/env python3
"""Fair control for the WINDOW rule on the 46 tight sets. Given that j* lies in L (the lonely set of the
four smaller elements), the null places it in a component with probability proportional to the
component's length. Expected hits = sum over sets of (longest component length) / (total length of L).
Also reports the rank of j*'s component by length."""
from fractions import Fraction as F
from collections import Counter
rows = [tuple(map(int, l.split())) for l in open("six_tight_dump_v1_100.txt")]
def lonely_set(R):
    ivs = [(F(0), F(1))]
    for p in R:
        bands = [(F(6*k + 1, 6*p), F(6*k + 5, 6*p)) for k in range(p)]
        ivs = [(max(a, c), min(b, d)) for a, b in ivs for c, d in bands if max(a, c) <= min(b, d)]
    return sorted(ivs)
hits = 0; expect = 0.0; ranks = Counter(); ncomp = []
for a, b, c, d, e, js in rows:
    L = lonely_set((a, b, c, d)); t = F(6 * js + 1, 6 * e)
    lens = [y - x for x, y in L]; mu = sum(lens)
    longest = max(range(len(L)), key=lambda i: lens[i])
    comp = next(i for i, (x, y) in enumerate(L) if x <= t <= y)
    hits += comp == longest; expect += float(lens[longest] / mu)
    order = sorted(range(len(L)), key=lambda i: -lens[i]); ranks[order.index(comp) + 1] += 1
    ncomp.append(len(L))
print(f"WINDOW: hits {hits}/{len(rows)}; expected under length-proportional null {expect:.2f}; ratio {hits/expect:.2f}")
print("rank (by length) of the component containing j*:", dict(sorted(ranks.items())))
print(f"components of L per set: min {min(ncomp)}, median {sorted(ncomp)[len(ncomp)//2]}, max {max(ncomp)}")
