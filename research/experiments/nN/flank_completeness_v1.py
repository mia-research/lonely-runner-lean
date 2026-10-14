# Is the one-sided flank family complete?  flankOpening n e j = (j + 1/n)/e puts e at 1/n AHEAD.
# On a circle a runner can also sit 1/n BEHIND, at t = (j + 1 - 1/n)/e.  If loneliness sometimes
# only happens there, `lonely_iff_exists_flank` would be undercounting and every criterion built
# on flankWorks would inherit it.
#
# POWER: at n=5 with 4 disparities everything is lonely, so that population cannot discriminate.
# Use 5 and 6 disparities at threshold 1/5 -- there, sets that are NOT lonely exist, so the
# statistic can come out either way.
from itertools import combinations
from fractions import Fraction as F
import math
n = 5
def lonely_bsm(ds):
    """Boundary Set Method: exact.  Critical points (m +- 1/n)/d; a cell is decided by its
    midpoint, and the critical points themselves are tested separately (the clear set can be
    isolated points -- that is the AP)."""
    pts = set()
    for d in ds:
        for m in range(0, d + 2):
            for off in (F(-1, n), F(1, n)):
                t = (F(m) + off) / F(d)
                if 0 < t <= 1: pts.add(t)
    P = sorted(pts)
    def clear(t):
        for d in ds:
            x = F(d) * t
            fr = x - (x.numerator // x.denominator)
            if min(fr, 1 - fr) < F(1, n): return False
        return True
    for t in P:                              # isolated clear points live here
        if clear(t): return True
    for i in range(len(P) - 1):              # and open cells are decided by a midpoint
        if clear((P[i] + P[i + 1]) / 2): return True
    return False
def flank_ahead(ds):
    for e in ds:
        M = n * e
        for j in range(e):
            if all(e <= (d * (n * j + 1)) % M <= (n - 1) * e for d in ds): return True
    return False
def flank_behind(ds):
    """the mirror family: e sits 1/n BEHIND, t = (j + 1 - 1/n)/e  ->  numerator n*j + n - 1"""
    for e in ds:
        M = n * e
        for j in range(e):
            if all(e <= (d * (n * j + n - 1)) % M <= (n - 1) * e for d in ds): return True
    return False
for k, HI in ((5, 14), (6, 12)):
    tot = lon = ah = be = 0; mismatch = []
    for c in combinations(range(1, HI + 1), k):
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        tot += 1
        L = lonely_bsm(c); A = flank_ahead(c); B = flank_behind(c)
        lon += L; ah += A; be += B
        if L != A and len(mismatch) < 6: mismatch.append((c, L, A, B))
    print(f"{k} disparities at threshold 1/5, entries <= {HI}:  {tot} primitive sets")
    print(f"   lonely (BSM, exact)      : {lon}   ({100*lon/tot:.2f}%)   <- both outcomes occur")
    print(f"   some AHEAD flank works   : {ah}")
    print(f"   some BEHIND flank works  : {be}")
    print(f"   lonely != ahead-flank    : {len(mismatch)} {'(none)' if not mismatch else mismatch}")
    print()
