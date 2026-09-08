r"""
ob_core_v1 -- exact primitives for the (H'') bound  o <= 1/3.

DEFINITIONS (all exact; Fraction / integer arithmetic only; no float in any decision)

  A "unit 4-tuple" is (e_1,e_3,e_5,e_7) of positive integers with e_rho = rho mod 8.
  Primitive means gcd(e_1,e_3,e_5,e_7) = 1.

  For x in [0,1):   t_rho = floor(e_rho x),  tau_rho = the odd member of {t,t+1},
                    s_rho = tau_rho mod 8 in (Z/8)^*.
  O  = { x : rho -> s_rho*rho is a bijection of (Z/8)^* },   o = |O|.

  KLEIN COORDINATE.  s_rho = 2 a_rho + 1 with a_rho = floor(e_rho x / 2) mod 4, and in
  the coordinate a = (u-1)/2 the group (Z/8)^* becomes (Z/2)^2 under XOR.  Writing
  mu_rho = (rho-1)/2, i.e. mu = 0,1,2,3 for rho = 1,3,5,7,

        nu_rho := a_rho XOR mu_rho ,     O = { x : nu_1,nu_3,nu_5,nu_7 all distinct }.

  QUADRANT COORDINATE.  a_rho(x) = floor(4*frac(e_rho * x/8)).  So with theta = x/8,
  a_rho is the QUADRANT index of e_rho*theta mod 1.  x in [0,1) <-> theta in [0,1/8);
  the "full-torus" variant integrates theta over all of [0,1).

This module supplies:
    o_x(tuple)        -- o over x in [0,1)          (cell method, ENTRY evaluation)
    o_torus(tuple)    -- o over theta in [0,1)      (quadrant grid, ENTRY evaluation)
    audit_x, audit_torus -- requirement (i) boundary audits
    collision_stats   -- exact p_ij, T_ijk, T_ij|kl  (needed by the moment bound)
"""
from fractions import Fraction as F
from math import gcd, lcm
from functools import reduce
import itertools

R4 = (1, 3, 5, 7)
MU = {1: 0, 3: 1, 5: 2, 7: 3}
MUV = (0, 1, 2, 3)               # mu for rho = 1,3,5,7


# ------------------------------------------------------------------ x in [0,1)
def _cellpts_x(speeds):
    """breakpoint numerators over D = lcm(speeds) for x in [0,1); floor(e x) is
    constant on each [p[i],p[i+1])."""
    D = reduce(lcm, speeds)
    s = set()
    for e in speeds:
        s.update(range(0, D, D // e))
    p = sorted(s)
    p.append(D)
    return D, p


def nu_at_x(speeds, D, a):
    """nu_rho at the cell ENTRY point a/D."""
    out = []
    for e, mu in zip(speeds, MUV):
        t = (e * a) // D                    # floor(e x)
        out.append(((t // 2) % 4) ^ mu)     # a_rho = floor(t/2) mod 4 = floor(e x /2) mod 4
    return tuple(out)


def o_x(speeds):
    D, p = _cellpts_x(speeds)
    tot = 0
    for i in range(len(p) - 1):
        if len(set(nu_at_x(speeds, D, p[i]))) == 4:
            tot += p[i + 1] - p[i]
    return F(tot, D)


def audit_x(speeds):
    """requirement (i): (1) no breakpoint k/e strictly inside a cell,
                        (2) entry floor == exit floor - [exit is integral]."""
    D, p = _cellpts_x(speeds)
    n_int = n_mis = 0
    for i in range(len(p) - 1):
        a, b = p[i], p[i + 1]
        for e in speeds:
            lo = (a * e) // D
            hi = (b * e) // D
            for k in range(lo + 1, hi + 1):
                if a * e < k * D < b * e:
                    n_int += 1
            entry = (a * e) // D
            exit_ = (b * e) // D - (1 if (b * e) % D == 0 else 0)
            if entry != exit_:
                n_mis += 1
    return len(p) - 1, n_int, n_mis


# ------------------------------------------------------------- theta in [0,1)
def _cellpts_t(speeds):
    """breakpoints of the quadrant functions floor(4 frac(e theta)):  j/(4e)."""
    D = reduce(lcm, [4 * e for e in speeds])
    s = set()
    for e in speeds:
        s.update(range(0, D, D // (4 * e)))
    p = sorted(s)
    p.append(D)
    return D, p


def quad_at(speeds, D, a):
    return tuple(((4 * e * a) // D) % 4 for e in speeds)


def o_torus(speeds):
    D, p = _cellpts_t(speeds)
    tot = 0
    for i in range(len(p) - 1):
        q = quad_at(speeds, D, p[i])
        if len(set(x ^ m for x, m in zip(q, MUV))) == 4:
            tot += p[i + 1] - p[i]
    return F(tot, D)


def audit_torus(speeds):
    D, p = _cellpts_t(speeds)
    n_int = n_mis = 0
    for i in range(len(p) - 1):
        a, b = p[i], p[i + 1]
        for e in speeds:
            f = 4 * e
            lo = (a * f) // D
            hi = (b * f) // D
            for k in range(lo + 1, hi + 1):
                if a * f < k * D < b * f:
                    n_int += 1
            entry = (a * f) // D
            exit_ = (b * f) // D - (1 if (b * f) % D == 0 else 0)
            if entry != exit_:
                n_mis += 1
    return len(p) - 1, n_int, n_mis


# ---------------------------------------------------------------- generation
def primitive_tuples(qmax):
    for qs in itertools.product(range(qmax + 1), repeat=4):
        e = tuple(8 * q + r for q, r in zip(qs, R4))
        if reduce(gcd, e) == 1:
            yield e


def relations(e):
    """+-1 vectors (sigma) with sum sigma_i e_i = 0, normalised sigma_1 = +1."""
    out = []
    for sg in itertools.product((1, -1), repeat=4):
        if sg[0] == 1 and sum(s * v for s, v in zip(sg, e)) == 0:
            out.append(sg)
    return out


# ------------------------------------------------- exact collision statistics
def _pair_measure(a, b, c):
    """|{ phi in [0,1) : floor(4 frac(a phi)) XOR floor(4 frac(b phi)) = c }|,
    gcd(a,b) = 1.   Exact; cells [j/(4ab), (j+1)/(4ab)) -- entry evaluation."""
    D = 4 * a * b
    tot = 0
    for j in range(D):
        qa = ((4 * a * j) // D) % 4
        qb = ((4 * b * j) // D) % 4
        if qa ^ qb == c:
            tot += 1
    return F(tot, D)


def p_pair(ei, ej, mui, muj):
    """P(nu_i = nu_j) exactly.  Depends only on (ei/g, ej/g, mui XOR muj)."""
    g = gcd(ei, ej)
    return _pair_measure(ei // g, ej // g, mui ^ muj)


if __name__ == "__main__":
    print("ob_core_v1 self-test")
    tests = [(1, 3, 5, 7), (1, 11, 5, 7), (17, 3, 5, 7), (1, 3, 13, 15),
             (9, 3, 21, 15), (25, 35, 5, 15), (41, 43, 13, 15), (33, 27, 13, 7)]
    print(f"{'tuple':>20} {'o_x':>12} {'o_torus':>12}  equal")
    for e in tests:
        ox, ot = o_x(e), o_torus(e)
        print(f"{str(e):>20} {str(ox):>12} {str(ot):>12}  {ox == ot}")
    print("\nboundary audits (cells, interior-breakpoints, entry!=exit):")
    for e in tests[:4]:
        print(f"   {str(e):>18}  x-grid {audit_x(e)}   theta-grid {audit_torus(e)}")
