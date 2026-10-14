r"""
ob_fast_v1 -- fast EXACT engine for o, validated against ob_core_v1.

o = |{ theta in [0,1) : (a_rho XOR mu_rho) all distinct }|,  a_rho = floor(4 frac(e_rho theta)).
(ob_core_v1 proves/checks this equals the x-in-[0,1) definition; see reports/n8_o_bound.md.)

The breakpoints of every a_rho are j/(4 e_rho).  Over D = lcm(4 e_rho) they are the
integers multiple of D/(4 e_rho).  All arithmetic is int64 (exact); the only float in
the module is in printing.  Cells are evaluated at the ENTRY point.

BOUNDARY EXACTNESS (requirement (i)) is enforced structurally: the breakpoint list is
the FULL preimage of the integers under theta -> 4 e_rho theta, so no breakpoint can
lie strictly inside a cell, and entry == exit is automatic.  `audit()` re-checks both
counts by brute force on demand.
"""
import numpy as np
from fractions import Fraction as F
from math import gcd, lcm
from functools import reduce

MUV = np.array([0, 1, 2, 3], dtype=np.int64)      # mu for rho = 1,3,5,7


def _grid(speeds):
    f = [4 * e for e in speeds]
    D = reduce(lcm, f)
    pts = np.unique(np.concatenate([np.arange(0, D, D // fi, dtype=np.int64) for fi in f]))
    return D, pts


def o_fast(speeds):
    """exact o as a Fraction"""
    D, pts = _grid(speeds)
    w = np.diff(np.append(pts, D))
    nu = np.empty((4, pts.size), dtype=np.int64)
    for i, e in enumerate(speeds):
        nu[i] = (((4 * e) * pts) // D) % 4 ^ MUV[i]
    # all four distinct  <=>  the 4 values are a permutation of 0..3
    bits = (1 << nu[0]) | (1 << nu[1]) | (1 << nu[2]) | (1 << nu[3])
    good = bits == 15
    return F(int(w[good].sum()), int(D))


def audit(speeds):
    """requirement (i), brute force: (interior breakpoints, entry!=exit) over all cells."""
    D, pts = _grid(speeds)
    b = np.append(pts[1:], D)
    n_int = n_mis = 0
    for e in speeds:
        f = 4 * e
        lo = (f * pts) // D
        hi = (f * b) // D
        # an interior breakpoint exists iff some integer k has a*f < k*D < b*f
        n_int += int(np.sum(hi - lo > ((f * b) % D == 0).astype(np.int64)))
        exit_ = hi - ((f * b) % D == 0).astype(np.int64)
        n_mis += int(np.sum(lo != exit_))
    return pts.size, n_int, n_mis


def relations(e):
    out = []
    for s3 in (1, -1):
        for s5 in (1, -1):
            for s7 in (1, -1):
                if e[0] + s3 * e[1] + s5 * e[2] + s7 * e[3] == 0:
                    out.append((1, s3, s5, s7))
    return out


if __name__ == "__main__":
    import itertools, random
    from ob_core_v1 import o_x, o_torus, primitive_tuples
    print("validation of ob_fast_v1.o_fast against ob_core_v1.o_x (exact Fractions)")
    bad = 0
    n = 0
    for e in primitive_tuples(3):
        n += 1
        if o_fast(e) != o_x(e):
            bad += 1
            print("   MISMATCH", e, o_fast(e), o_x(e))
    print(f"   exhaustive q<=3: {n} tuples, mismatches {bad}")
    random.seed(7)
    bad = 0
    for _ in range(60):
        e = tuple(8 * random.randrange(0, 30) + r for r in (1, 3, 5, 7))
        if reduce(gcd, e) != 1:
            continue
        if o_fast(e) != o_x(e):
            bad += 1
            print("   MISMATCH", e)
    print(f"   60 random tuples with speeds <= 240: mismatches {bad}")
    print("\n   boundary audit (cells, interior-breakpoints, entry!=exit):")
    for e in [(1,3,5,7),(17,3,5,7),(1,11,5,7),(241,163,205,199)]:
        print(f"      {str(e):>20} {audit(e)}")
