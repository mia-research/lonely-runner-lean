"""Exact clear-set machinery. All decisions in Fraction."""
from fractions import Fraction as F
from math import floor, ceil

EIGHT = 8

def good_intervals(x, Rlo, Rhi):
    """Closed R-intervals within [Rlo,Rhi] where (x*R) mod 8 in [1,7]  (x>0 Fraction)."""
    out = []
    k0 = floor((x * Rlo - 7) / 8)
    k = max(k0, 0)
    while True:
        a = F(8 * k + 1) / x
        b = F(8 * k + 7) / x
        if a > Rhi:
            break
        lo, hi = max(a, Rlo), min(b, Rhi)
        if lo <= hi:
            out.append((lo, hi))
        k += 1
    return out

def intersect(A, B):
    """Intersect two sorted lists of disjoint closed intervals."""
    i = j = 0
    out = []
    while i < len(A) and j < len(B):
        lo = max(A[i][0], B[j][0]); hi = min(A[i][1], B[j][1])
        if lo <= hi:
            out.append((lo, hi))
        if A[i][1] < B[j][1]:
            i += 1
        else:
            j += 1
    return out

def clear_set(s, Rlo=F(1), Rhi=F(15)):
    S = [(F(Rlo), F(Rhi))]
    for x in s:
        S = intersect(S, good_intervals(F(x), F(Rlo), F(Rhi)))
        if not S:
            return S
    return S

def least_clear(s, Rhi=F(40)):
    S = clear_set(s, F(1), F(Rhi))
    return S[0][0] if S else None

def is_clear(s, R):
    R = F(R)
    for x in s:
        r = (F(x) * R) % 8
        if r < 1 or r > 7:
            return False
    return True
