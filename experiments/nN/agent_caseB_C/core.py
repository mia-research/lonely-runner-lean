"""Core exact machinery for the Case B grid-class study.

Every decision uses fractions.Fraction (or Python int, which is exact).
Readings are passed as a tuple of Fractions (or ints); the problem is scale
invariant, so an integer set a_0 < ... < a_6 may be passed unnormalised.

Setting.  Reading s is CLEAR at R iff (s R) mod 8 in [1,7].
Grid class (j, m, c): lambda = s_j/m, x_i = s_i/lambda = m s_i/s_j,
n_i in {floor x_i, ceil x_i}, n_i >= 1, k_i = floor(c n_i / 8)
(k_i or k_i - 1 when c n_i = 0 mod 8).  The class WORKS iff the R-intervals
[(8k_i+1)/s_i, (8k_i+7)/s_i] have a common point (P1, 1-D Helly).
"""
from fractions import Fraction as F
from math import floor, ceil

CLASSES = (1, 3, 5, 7)


def fl(q):
    q = F(q)
    return q.numerator // q.denominator


def ce(q):
    q = F(q)
    return -((-q.numerator) // q.denominator)


def clear(s, R):
    """Exact: (s R) mod 8 in [1,7]."""
    v = F(s) * F(R)
    r = v - 8 * fl(v / 8)
    return 1 <= r <= 7


def lonely_at(S, R):
    return all(clear(s, R) for s in S)


def grid_ns(x):
    """Admissible grid points for position x: floor/ceil, n >= 1."""
    a, b = fl(x), ce(x)
    out = {a, b}
    return sorted(n for n in out if n >= 1) or [1]


def laps(c, n):
    t = c * n
    if t % 8 == 0:
        return [t // 8, t // 8 - 1]
    return [t // 8]


def reading_options(S, j, m, c, i, allow_capture=True):
    """List of (n, k, residue, lo, hi) R-intervals for reading i."""
    s = F(S[i])
    x = F(m) * s / F(S[j])
    out = []
    for n in grid_ns(x):
        r = (c * n) % 8
        if r == 0 and not allow_capture:
            continue
        for k in laps(c, n):
            if k < 0:
                continue
            out.append((n, k, r, F(8 * k + 1) / s, F(8 * k + 7) / s))
    return out


def class_works(S, j, m, c, allow_capture=True, filt=None):
    """Return a witness R (Fraction) if the class (j,m,c) works, else None.

    Intersection of unions of closed intervals is nonempty iff some left
    endpoint lies in every union (max of the chosen left endpoints).
    filt(i, n, k, r) -> bool optionally restricts options.
    """
    U = []
    for i in range(len(S)):
        opts = [(lo, hi) for (n, k, r, lo, hi) in reading_options(S, j, m, c, i, allow_capture)
                if filt is None or filt(i, n, k, r)]
        if not opts:
            return None
        U.append(opts)
    cands = sorted({lo for opts in U for (lo, hi) in opts})
    for p in cands:
        if all(any(lo <= p <= hi for (lo, hi) in opts) for opts in U):
            return p
    return None


def working_options(S, M=4, allow_capture=True):
    """Yield (m, j, c, R) for every working class with m <= M."""
    for m in range(1, M + 1):
        for j in range(len(S)):
            for c in CLASSES:
                R = class_works(S, j, m, c, allow_capture)
                if R is not None:
                    yield (m, j, c, R)


def least_m(S, M=4, allow_capture=True):
    for m in range(1, M + 1):
        for j in range(len(S)):
            for c in CLASSES:
                R = class_works(S, j, m, c, allow_capture)
                if R is not None:
                    assert lonely_at(S, R)
                    return m, j, c, R
    return None


def integer_caseB(maxv=24, lo_ratio=7, hi_ratio=24):
    """All 7-sets of distinct integers in [1,maxv] with lo < a6/a0 <= hi."""
    from itertools import combinations
    for a0 in range(1, maxv + 1):
        for a6 in range(a0 + 6, maxv + 1):
            if not (lo_ratio * a0 < a6 <= hi_ratio * a0):
                continue
            for mid in combinations(range(a0 + 1, a6), 5):
                yield (a0,) + mid + (a6,)


def normalise(A):
    a0 = F(A[0])
    return tuple(F(a) / a0 for a in A)
