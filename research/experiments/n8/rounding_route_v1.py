"""Derived route for LARGE quotients: the 6 speeds {1, s_i} at t = q/m is LRC at order 7
(proved, threshold 1/7).  Rounding t to a multiple of 1/m costs <= s_i/(2m) = 1/(2 b_i).
Margin 1/7 - 1/8 = 1/56 survives iff b_i >= 28.

Test the ARITHMETIC of the route, not the conclusion: find a real order-7 witness t, round it,
and check the rounded q clears.  If the derivation is right, 0 failures once all b_i >= 28.
"""
from fractions import Fraction as F
from itertools import combinations
import random

def norm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1-f)

def find_t(speeds, thr, m):
    """A real witness at threshold thr, searched on a fine grid independent of m."""
    D = 8*m*7
    for j in range(1, D):
        t = F(j, D)
        if all(norm(s*t) >= thr for s in speeds): return t
    return None

def blocks(si, A, sk):
    M = 8*sk; r = (si*A) % M
    return min(r, M-r) < sk

rng = random.Random(20260919)
for lo_b, label in ((28, "all middle b_i >= 28  (the derived threshold)"),
                    (12, "all middle b_i >= 12  (below it)"),
                    (8,  "all middle b_i >= 8   (well below)")):
    tot = no_t = fail = 0
    for m in range(8, 4000):
        ds = [d for d in range(2, m) if m % d == 0 and m//d >= lo_b]
        if len(ds) < 5: continue
        for _ in range(3):
            sub = tuple(sorted(rng.sample(ds, 5)))
            S = tuple(sorted({1, m} | set(sub)))
            if len(S) != 7: continue
            tot += 1
            t = find_t([1] + list(sub), F(1,7), m)
            if t is None: no_t += 1; continue
            q = round(t * m)
            A = 8*q + 1
            if not (m <= A <= 7*m) or any(blocks(si, A, m) for si in S): fail += 1
        if tot > 900: break
    print(f"  {label:<44} {tot:>5} profiles   rounding FAILED {fail:>4}"
          f"   (no real witness: {no_t})")
