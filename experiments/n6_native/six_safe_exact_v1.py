#!/usr/bin/env python3
"""E41: exact two-window SAFE decision. Geometry (alpha, beta, gamma, rho) in runner-4 laps, rational.
Starts (a4, a5) <-> lines of slope rho: point (s, c + rho s), c in [0,1), position s0 in [0,1) (covers the torus).
Along line c, K(c) = { s : frac(s) in [1/6,5/6] and frac(c + rho s) in [1/6,5/6] } (runners 4 and 5 both clear),
a union of closed intervals. Windows fail iff [s0, s0+alpha] and [s0+delta, s0+delta+gamma] (delta = alpha+beta)
both miss K(c). The failing set is open in (c, s0). For fixed c, the set of good s0 is a finite union of open
intervals computed exactly; its combinatorics changes only at critical c where an endpoint difference of K equals a
window constant (or two endpoints coincide). Endpoints: runner-4 ends i + 1/6, i + 5/6 (constant), runner-5 ends
(j + e - c)/rho, e in {1/6, 5/6} (slope -1/rho). Critical c: for every runner-4 end A, runner-5 index j, e, and
kappa in {0, +-alpha, +-gamma, +-delta, +-(delta - alpha), +-(delta + gamma), +-(delta + gamma - alpha), +-(gamma - alpha)}:
(j + e - c)/rho = A + kappa. Runner-5 / runner-5 and 4 / 4 differences do not depend on c. Decide at the midpoint
of every slab between consecutive critical c (and at the critical values too). Exact Fractions throughout.
SAFE <=> no failing (c, s0)."""
import math
from fractions import Fraction as F
s6, s56 = F(1, 6), F(5, 6)
def clear_set(c, rho, lo, hi):
    """K(c) on [lo, hi] as sorted closed intervals."""
    A = []
    for i in range(math.floor(lo) - 1, math.ceil(hi) + 1):
        A.append((i + s6, i + s56))
    out = []
    jlo = math.floor(c + rho * lo) - 1; jhi = math.ceil(c + rho * hi) + 1
    for j in range(jlo, jhi + 1):
        b0, b1 = (j + s6 - c) / rho, (j + s56 - c) / rho
        for a0, a1 in A:
            x, y = max(a0, b0), min(a1, b1)
            if x <= y and y >= lo and x <= hi: out.append((x, y))
    return sorted(out)
def good_s0(c, rho, alpha, delta, gamma):
    """open intervals of s0 in [0,1) where both windows miss K(c) (exact)."""
    K = clear_set(c, rho, F(-2), F(1) + delta + gamma + 2)
    # free gaps: open intervals between consecutive clear pieces
    gaps = []
    for (x0, y0), (x1, y1) in zip(K, K[1:]):
        if y0 < x1: gaps.append((y0, x1))
    def fit(L):
        # s with [s, s+L] inside a free gap: s in (g0, g1 - L)
        return [(g0, g1 - L) for g0, g1 in gaps if g1 - L > g0]
    W1 = fit(alpha); W3 = [(a - delta, b - delta) for a, b in fit(gamma)]
    res = []
    for a, b in W1:
        for c2, d in W3:
            lo, hi = max(a, c2, F(0)), min(b, d, F(1))
            if lo < hi: res.append((lo, hi))
    return res
def critical(rho, alpha, beta, gamma):
    delta = alpha + beta
    ks = {F(0), alpha, gamma, delta, delta - alpha, delta + gamma, delta + gamma - alpha, gamma - alpha}
    ks |= {-k for k in ks}
    smax = 1 + delta + gamma + 2
    As = [i + e for i in range(-3, math.ceil(smax) + 2) for e in (s6, s56)]
    crit = set()
    for A in As:
        for k in ks:
            for e in (s6, s56):
                # (j + e - c)/rho = A + k  ->  c = j + e - rho (A + k); reduce mod 1
                base = e - rho * (A + k)
                crit.add(base - math.floor(base))
    crit |= {F(0), F(1)}
    return sorted(crit)
def safe_exact(alpha, beta, gamma, rho):
    delta = alpha + beta
    cs = critical(rho, alpha, beta, gamma)
    tests = cs[:-1] + [(a + b) / 2 for a, b in zip(cs, cs[1:])]
    for c in tests:
        g = good_s0(c, rho, alpha, delta, gamma)
        if g: return False, (c, g[0])
    return True, None
if __name__ == "__main__":
    import sys
    # control: delta = 0, gamma = alpha reduces to one window; unsafe just below L(rho), safe at L(rho)
    def Lform(rho):
        m = max(-(-(rho + 1) // 3) - 1, 0)
        return max(F(1, 3) + 1 / (3 * rho), (m + F(1, 3)) / rho)
    bad = 0; n = 0
    for rho in [F(1), F(11, 10), F(3, 2), F(2), F(5, 2), F(3), F(7, 2), F(4), F(11, 2), F(7)]:
        L = Lform(rho)
        below, _ = safe_exact(L - F(1, 1000), -(L - F(1, 1000)), L - F(1, 1000), rho)
        at, _ = safe_exact(L, -L, L, rho)
        n += 1; bad += (below or not at)
        print(f"rho {rho}: L = {L}; SAFE just below L: {below} (expect False); SAFE at L: {at} (expect True)")
    print("control failures:", bad, "of", n)
