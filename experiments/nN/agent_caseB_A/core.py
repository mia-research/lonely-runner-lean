"""Exact core for the band covering argument (agent_caseB_A).

Representation: a set is a tuple of seven positive integers n0 < n1 < ... < n6.
Readings are s_i = n_i / n0 (so s0 = 1).  Band: 7*n0 < n6 <= 9*n0.
All decisions are integer or Fraction arithmetic.  No floating point.

Clear at R (R a Fraction):  (s*R) mod 8 in [1, 7].
Block (e, K): R = (8K+1)/s_e = (8K+1)*n0/n_e.  Reading d is clear there iff
    ((8K+1)*n_d) mod (8*n_e)  in  [n_e, 7*n_e].
"""
from fractions import Fraction as F
from itertools import combinations

RANGE = ((F(1), F(7)), (F(9), F(15)))


def in_range(R):
    return any(lo <= R <= hi for lo, hi in RANGE)


def clear(n, n0, R):
    """reading n/n0 clear at R (exact)."""
    x = F(n, n0) * R
    m = x - 8 * (x.numerator // (8 * x.denominator))
    return 1 <= m <= 7


def lonely_at(ns, R):
    n0 = ns[0]
    return all(clear(n, n0, R) for n in ns)


def block_ok(ns, e, K):
    """block rule at reading index e, level K (integer test)."""
    ne = ns[e]
    m = 8 * K + 1
    lo, hi, mod = ne, 7 * ne, 8 * ne
    for nd in ns:
        r = (m * nd) % mod
        if r < lo or r > hi:
            return False
    return True


def block_R(ns, e, K):
    return F(8 * K + 1) * ns[0] / ns[e]


def candidates(ns):
    """all (R, e, K) block points with R in range, sorted by R."""
    out = []
    n0 = ns[0]
    for e, ne in enumerate(ns):
        K = 0
        while True:
            R = F(8 * K + 1) * n0 / ne
            if R > 15:
                break
            if in_range(R):
                out.append((R, e, K))
            K += 1
    out.sort()
    return out


def landing(ns):
    """least R in [1,7] u [9,15] where the set is lonely, or None.
    Complete: every component of the lonely set starts at some block point."""
    for R, e, K in candidates(ns):
        if block_ok(ns, e, K):
            return (R, e, K)
    return None


def lonely_intervals(ns):
    """exact lonely set inside [1,7] u [9,15] as a list of closed intervals."""
    n0 = ns[0]
    res = []
    for lo, hi in RANGE:
        cur = [(lo, hi)]
        for nd in ns[1:]:
            s = F(nd, n0)
            new = []
            for a, b in cur:
                k = 0
                while True:
                    wl, wr = F(8 * k + 1) / s, F(8 * k + 7) / s
                    if wl > b:
                        break
                    L, Rr = max(a, wl), min(b, wr)
                    if L <= Rr:
                        new.append((L, Rr))
                    k += 1
            cur = new
        res.extend(cur)
    return res


def least_level(ns):
    """least K such that some reading e works at block level K with R in range."""
    best = None
    for R, e, K in candidates(ns):
        if block_ok(ns, e, K):
            if best is None or K < best[0]:
                best = (K, e, R)
    return best


# ---------------------------------------------------------------- datasets

def integer_band_sets(maxv):
    """all 7-subsets of {1..maxv} with 7*n0 < n6 <= 9*n0."""
    for n0 in range(1, maxv + 1):
        for n6 in range(7 * n0 + 1, min(9 * n0, maxv) + 1):
            mids = range(n0 + 1, n6)
            for c in combinations(mids, 5):
                yield (n0,) + c + (n6,)


def is_band(ns):
    return (all(ns[i] < ns[i + 1] for i in range(6)) and 7 * ns[0] < ns[6] <= 9 * ns[0]
            and ns[0] > 0)
