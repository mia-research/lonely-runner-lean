#!/usr/bin/env python3
"""Tight sets (one good opening at the largest flank), from six_tight_dump_v1_100.txt.
(1) The four smaller elements reduced by their gcd: which primitive patterns P occur.
(2) For each pattern, the exact measure mu(P) of {t in [0,1): every p in P has ||p t|| >= 1/6},
    computed as a union of intervals with exact Fractions (each p contributes the bands
    [(k+1/6)/p, (k+5/6)/p]); compared with G/e for sets whose small part is a multiple of P.
(3) Readings at the unique opening: which elements sit exactly on the band boundary (residue e or 5e)."""
import math
from fractions import Fraction as F
from collections import Counter, defaultdict
rows = [tuple(map(int, l.split())) for l in open("six_tight_dump_v1_100.txt")]
def lonely_measure(P):
    # intersect, over p in P, the clear sets within [0,1)
    ivs = [(F(0), F(1))]
    for p in P:
        bands = [(F(6*k + 1, 6*p), F(6*k + 5, 6*p)) for k in range(p)]
        new = []
        for a, b in ivs:
            for c, d in bands:
                lo, hi = max(a, c), min(b, d)
                if lo < hi: new.append((lo, hi))
        ivs = new
    return sum(b - a for a, b in ivs)
pat = Counter(); by_pat = defaultdict(list); boundary = Counter()
for a, b, c, d, e, j in rows:
    small = (a, b, c, d); g = math.gcd(*small)
    P = tuple(x // g for x in small)
    pat[P] += 1; by_pat[P].append((g, e, j))
    m = 6 * j + 1
    on = tuple(x for x in (a, b, c, d) if (x * m) % (6 * e) in (e, 5 * e))
    boundary[len(on)] += 1
print(f"tight sets: {len(rows)}; distinct primitive small patterns: {len(pat)}")
for P, cnt in pat.most_common():
    mu = lonely_measure(P)
    print(f"  P={P}: {cnt} sets; mu(P)={mu} = {float(mu):.4f}; members (scale g, e, j*): {by_pat[P][:6]}")
print("  number of small elements exactly on a band boundary at the unique opening:", dict(sorted(boundary.items())))
