r"""
nr2_core  --  exact machinery for the n = 8 Unit-Complete leaf,
              |E_non| = 5, |E_div| = 2, NON-representative base speeds.

Everything is exact integer / Fraction arithmetic.  No float ever enters a decision.

CONVENTIONS
-----------
bad(e,t) = { r in Z/8 : (e*r + t) mod 8 in {0,7} }.  It depends on e only through
rho = e mod 8 and on t only through t mod 8 (PAIR RULE, given).

A cell is a half-open interval [a,b) between consecutive breakpoints j/e, e in the
speed tuple.  Cells are represented by integer numerators over the common
denominator D = lcm(speeds).  On a cell, floor(e*x) is constant and equals the
ENTRY value (e*a)//D.  Never a midpoint (BOUNDARY EXACTNESS requirement (i)).

The five base runners are e_rho = 8 q_rho + rho for rho in R = {1,3,5,7,rho0}.
"""
from math import lcm, gcd
from fractions import Fraction as F
import itertools

# ---------------------------------------------------------------- bad sets
BADSET = {(rho, t): frozenset(r for r in range(8) if (rho * r + t) % 8 in (0, 7))
          for rho in range(8) for t in range(8)}
MASK = {k: sum(1 << r for r in v) for k, v in BADSET.items()}

ALL = 255
ODD = sum(1 << r for r in (1, 3, 5, 7))          # 0b10101010 = 170
EVEN = sum(1 << r for r in (0, 2, 4, 6))         # 0b01010101 = 85

OMASK = {k: m & ODD for k, m in MASK.items()}
EMASK = {k: m & EVEN for k, m in MASK.items()}


# ---------------------------------------------------------------- cells
def cell_table(speeds):
    """Return (D, pts) with pts the sorted list of breakpoint numerators over D,
    terminated by D.  Cells are [pts[i], pts[i+1])."""
    D = lcm(*speeds)
    s = set()
    for e in speeds:
        step = D // e
        s.update(range(0, D, step))
    p = sorted(s)
    p.append(D)
    return D, p


def states_at(speeds, D, a):
    """floor(e*a/D) mod 8 for each speed, evaluated at the cell ENTRY point a."""
    return tuple(((e * a) // D) % 8 for e in speeds)


# ------------------------------------------------- the four quantities we need
def _sweep(speeds, rhos, predicate):
    """total width (over D) of the cells whose entry state satisfies predicate"""
    D, p = cell_table(speeds)
    tot = 0
    for i in range(len(p) - 1):
        a = p[i]
        st = tuple(((e * a) // D) % 8 for e in speeds)
        if predicate(rhos, st):
            tot += p[i + 1] - a
    return tot, D


def _cov(rhos, st):
    c = 0
    for rho, t in zip(rhos, st):
        c |= MASK[(rho, t)]
    return c


def safe_measure(speeds, rhos):
    """|S| : the base runners leave some residue uncovered."""
    n, d = _sweep(speeds, rhos, lambda R, s: _cov(R, s) != ALL)
    return F(n, d)


def blocked_measure(speeds, rhos):
    n, d = _sweep(speeds, rhos, lambda R, s: _cov(R, s) == ALL)
    return F(n, d)


def o_measure(unit_speeds):
    """o = |O|, O = { x : the four unit runners cover ALL FOUR odd residues }."""
    R = (1, 3, 5, 7)
    def pred(_R, st):
        c = 0
        for rho, t in zip(R, st):
            c |= OMASK[(rho, t)]
        return c == ODD
    n, d = _sweep(unit_speeds, R, pred)
    return F(n, d)


def v_measure(unit_speeds):
    R = (1, 3, 5, 7)
    def pred(_R, st):
        c = 0
        for rho, t in zip(R, st):
            c |= EMASK[(rho, t)]
        return c == EVEN
    n, d = _sweep(unit_speeds, R, pred)
    return F(n, d)


def u_measure(unit_speeds):
    R = (1, 3, 5, 7)
    n, d = _sweep(unit_speeds, R, lambda _R, st: _cov(R, st) == ALL)
    return F(n, d)


# ------------------------------------------------------- interval machinery
def components(speeds, rhos, predicate):
    """maximal half-open components (as Fractions) of the set of x whose entry state
    satisfies `predicate`.  Wrap-aware: if the set contains a neighbourhood of 0 and
    of 1 the two end components are reported separately (caller merges if it wants
    the circle picture)."""
    D, p = cell_table(speeds)
    out = []
    for i in range(len(p) - 1):
        a = p[i]
        st = tuple(((e * a) // D) % 8 for e in speeds)
        if predicate(rhos, st):
            if out and out[-1][1] == a:
                out[-1][1] = p[i + 1]
            else:
                out.append([a, p[i + 1]])
    return [(F(u, D), F(v, D)) for u, v in out], D


def O_components(unit_speeds):
    R = (1, 3, 5, 7)
    def pred(_R, st):
        c = 0
        for rho, t in zip(R, st):
            c |= OMASK[(rho, t)]
        return c == ODD
    return components(unit_speeds, R, pred)


def V_components(unit_speeds):
    R = (1, 3, 5, 7)
    def pred(_R, st):
        c = 0
        for rho, t in zip(R, st):
            c |= EMASK[(rho, t)]
        return c == EVEN
    return components(unit_speeds, R, pred)


# -------------------------------------------------- BOUNDARY EXACTNESS audit
def boundary_audit(speeds):
    """Requirement (i).  For every cell [a,b) (numerators over D) and every speed e:

       (1) COMPLETENESS: no integer k with a/D < k/e < b/D.
       (2) ENTRY == EXIT: floor(e*a/D) == floor(e*b/D) - [e*b/D in Z].

    Returns (n_cells, n_interior_breakpoints, n_entry_exit_mismatches).
    All comparisons are exact integer comparisons."""
    D, p = cell_table(speeds)
    n_int = 0
    n_mis = 0
    for i in range(len(p) - 1):
        a, b = p[i], p[i + 1]
        for e in speeds:
            # (1) integers k with a*e/D < k < b*e/D
            lo = (a * e) // D                     # floor(a e / D)
            hi = (b * e) // D
            # candidate interior k are lo+1 .. hi (k/e strictly inside (a/D, b/D))
            for k in range(lo + 1, hi + 1):
                if a * e < k * D < b * e:
                    n_int += 1
            # (2) entry vs exit
            entry = (a * e) // D
            exit_ = (b * e) // D - (1 if (b * e) % D == 0 else 0)
            if entry != exit_:
                n_mis += 1
    return len(p) - 1, n_int, n_mis


# ---------------------------------------------------------- P-sets for rho0
def P_sets(rho0, q0):
    """The two half-open periodic sets of the PARITY REDUCTION, as (list of
    (a,b) Fractions, duty).  e_rho0 = 8 q0 + rho0.

      rho0 in {2,6}:  P_odd  = { x : floor(e x) mod 8 in {1,2,5,6} }  (bad is a pair
                                of ODD residues there)  -- duty 1/2
                      P_even = complement                              -- duty 1/2
      rho0 = 4     :  P_even = { t mod 8 != 3,4 } (bad is even or empty) duty 3/4
                      P_odd  = { t mod 8 in {3,4} }                     duty 1/4

    Returned as (P_even_intervals, P_odd_intervals)."""
    e = 8 * q0 + rho0
    if rho0 in (2, 6):
        odd_t, even_t = {1, 2, 5, 6}, {0, 3, 4, 7}
    elif rho0 == 4:
        odd_t, even_t = {3, 4}, {0, 1, 2, 5, 6, 7}
    else:
        raise ValueError(rho0)
    Pe, Po = [], []
    for j in range(e):
        iv = (F(j, e), F(j + 1, e))
        (Po if j % 8 in odd_t else Pe).append(iv)
    return merge(Pe), merge(Po)


def merge(ivs):
    ivs = sorted([list(v) for v in ivs])
    out = []
    for a, b in ivs:
        if out and a <= out[-1][1]:
            out[-1][1] = max(out[-1][1], b)
        else:
            out.append([a, b])
    return [tuple(v) for v in out]


def inter_measure(A, B):
    """measure of the intersection of two sorted lists of disjoint half-open intervals"""
    i = j = 0
    tot = F(0)
    while i < len(A) and j < len(B):
        lo = max(A[i][0], B[j][0])
        hi = min(A[i][1], B[j][1])
        if lo < hi:
            tot += hi - lo
        if A[i][1] < B[j][1]:
            i += 1
        else:
            j += 1
    return tot


if __name__ == "__main__":
    print("nr2_core self-test")
    print("  |bad| table: rho odd -> 2 elements, one odd one even:",
          all(len(BADSET[(r, t)]) == 2 and
              len([a for a in BADSET[(r, t)] if a % 2]) == 1
              for r in (1, 3, 5, 7) for t in range(8)))
    print("  rho in {2,6} -> coset of {0,4}, single parity:",
          all(len(BADSET[(r, t)]) == 2 and
              len({a % 2 for a in BADSET[(r, t)]}) == 1 and
              {(a - b) % 8 for a in BADSET[(r, t)] for b in BADSET[(r, t)]} == {0, 4}
              for r in (2, 6) for t in range(8)))
    print("  rho = 4 -> evens / odds / empty:",
          sorted({tuple(sorted(BADSET[(4, t)])) for t in range(8)}))
    print("  representative checks: |S(1,3,5,7,2)| =", safe_measure((1, 3, 5, 7, 2), (1, 3, 5, 7, 2)),
          " |S(1,3,5,7,4)| =", safe_measure((1, 3, 5, 7, 4), (1, 3, 5, 7, 4)),
          " |S(1,3,5,7,6)| =", safe_measure((1, 3, 5, 7, 6), (1, 3, 5, 7, 6)))
    print("  o(1,3,5,7) =", o_measure((1, 3, 5, 7)), " v =", v_measure((1, 3, 5, 7)),
          " u =", u_measure((1, 3, 5, 7)))
