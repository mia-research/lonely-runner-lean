#!/usr/bin/env python3
"""Exact leaf data for §5 k = 1, alpha <= 1/50 (fractions; conservative per-term bounds as the Lean checks use them).
(A) runner-4 leaves (runner 5 folded, mu0 = 1/3): lam in [l0, l1], lap shift m, P-interval [pa, pb] with pa >= 1/6,
    pb <= 1/3, pb - pa >= 1/50:  m - 1/3 <= (l0 - 1) pa  and  l1 pb <= m + 1/3.  Cover (1, 25/14] and [16/5, 23].
(B) strip leaves with mu0 = 1064/5000 (gamma >= 2/3 there; mu <= (1 + beta)/5 <= 1.064/5): conditions
    m - (2/3 - P) + mu0 <= lam P <= m + 2/3 - mu0 and mu0 <= 2/3 - P for P in [pa, pb]:
    m - 2/3 + mu0 <= (l0 - 1) pa,  l1 pb <= m + 2/3 - mu0,  pb <= 2/3 - mu0.  Cover [25/14, 16/5].
(S) (lam, lam5) tree over [25/14, 16/5] x [lam, 30], ivt_box leaves: n1, m3, m4, m5, pa, pb, pb - pa >= 1/50; check each
    pairwise condition up_k - low_i >= 0 with term-wise bounds (constant + P-term + lam P-term + lam5 P-term, each
    bounded by its worst corner).
(R5) one 4-runner interval over the whole strip, length >= 1/(30 - 16/5) + 2/90."""
import math
from fractions import Fraction as F
def greedy(lo, hi, leaf_for):
    out = []; l0 = lo
    while l0 < hi:
        best = None
        # largest l1 (on a grid) admitting a leaf
        step = (hi - l0)
        while step > F(1, 2000):
            l1 = min(hi, l0 + step)
            lf = leaf_for(l0, l1)
            if lf: best = (l1, lf); break
            step /= 2
        if not best: raise SystemExit(f"stuck at {float(l0)}")
        out.append((l0, best[0]) + best[1]); l0 = best[0]
    return out
W = F(1, 50)
def leafA(l0, l1):
    for m in range(0, 12):
        # choose pa as small as allowed: pa >= 1/6 and (l0 - 1) pa >= m - 1/3
        pa = max(F(1, 6), (F(m) - F(1, 3)) / (l0 - 1)) if l0 > 1 else F(1, 6)
        pb = pa + W
        if pb <= F(1, 3) and (F(m) - F(1, 3)) <= (l0 - 1) * pa and l1 * pb <= F(m) + F(1, 3): return (m, pa, pb)
    return None
MU0 = F(1064, 5000)
def leafB(l0, l1):
    for m in range(0, 6):
        pa = max(F(1, 6), (F(m) - F(2, 3) + MU0) / (l0 - 1))
        pb = pa + W
        if pb <= F(2, 3) - MU0 and l1 * pb <= F(m) + F(2, 3) - MU0 and F(m) - F(2, 3) + MU0 <= (l0 - 1) * pa: return (m, pa, pb)
    return None
A1 = greedy(F(1), F(25, 14), leafA) if leafA(F(1), F(25, 14)) is None else [(F(1), F(25, 14)) + leafA(F(1), F(25, 14))]
A2 = greedy(F(16, 5), F(23), leafA)
B = greedy(F(25, 14), F(16, 5), leafB)
print("A (lam <= 25/14):", [(float(a), float(b), m, str(pa), str(pb)) for a, b, m, pa, pb in A1])
print("A (16/5 .. 23):", len(A2), [(float(a), float(b), m) for a, b, m, pa, pb in A2])
print("B (strip, gamma >= 2/3):", [(float(a), float(b), m, str(pa), str(pb)) for a, b, m, pa, pb in B])
import pickle; pickle.dump((A1, A2, B), open("s5k1_small_gen_v1.pkl", "wb"))
