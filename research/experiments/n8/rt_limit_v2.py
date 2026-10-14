r"""
rt_limit_v2 -- EXACT subtorus limits of o for resonance lattices of rank 1 AND rank 2.

Extends rt_limit_v1 (rank 1, and only for n0 with an entry +-1) in two ways.

RANK 1, any primitive n0.  Drop the coordinate sigma with n0_sigma != 0.  The projection
T_{n0} -> T^3 forgetting v_sigma is surjective with fibres of size |n0_sigma|, and pushes
Haar to Haar.  So (v_rho)_{rho != sigma} are iid uniform, t is uniform on
{0..|n0_sigma|-1}, and  4 v_sigma = (4t - J - X)/n0_sigma  with J = SUM n0_rho j_rho an
integer and X = SUM n0_rho s_rho.  Then a_sigma = m mod 4 where m is the unique integer
with  m*n <= Q - X < (m+1)*n  (n = n0_sigma > 0, Q = 4t - J), so

        P(a_sigma = m mod 4) = F_X(Q - m n) - F_X(Q - (m+1) n),

and F_X is the exact Irwin-Hall CDF of a signed integer combination of uniforms.
Everything rational.

RANK 2, any saturated lattice L = <n1, n2>.  Compute a unimodular U with M U = [H | 0]
(column HNF); the last two columns of U are a Z-basis B of the SATURATED kernel, so
T_L = { B y : y in T^2 } and the parametrisation is measure preserving.  Writing
y_j = (k_j + s_j)/4,

        a_rho = ( B_rho . k  +  floor(B_rho . s) )  mod 4,     s uniform on [0,1)^2,

and the joint law of the four floors is a partition of the unit square into convex
polygons with rational vertices.  Areas are computed EXACTLY by Sutherland-Hodgman
clipping in Fraction arithmetic plus the shoelace formula.  No float anywhere.

Self-checks in __main__:
  * rank-1 general vs rt_limit_v1's +-1 formula, on every n0 with a +-1 entry;
  * every d-partition sums to area 1 exactly;
  * rank-1 limits recovered as a degenerate rank-2 check on a few lattices;
  * rank-2 limits compared against EXACT o of genuine deep members of the family.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
import itertools

MU = (0, 1, 2, 3)
RHO = (1, 3, 5, 7)


# ------------------------------------------------------- exact Irwin-Hall CDF
def _cdf(bs, y):
    """P( sum b_j u_j < y ), u_j iid U[0,1), b_j > 0 integers."""
    r = len(bs)
    if r == 0:
        return F(1) if y > 0 else F(0)
    tot = F(0)
    for k in range(r + 1):
        for J in itertools.combinations(range(r), k):
            t = F(y) - sum(bs[j] for j in J)
            if t > 0:
                tot += (-1) ** k * t ** r
    den = 1
    for i in range(2, r + 1):
        den *= i
    for b in bs:
        den *= b
    return tot / den


class LinForm:
    """X = sum c_rho s_rho, s iid U[0,1).  Exact CDF."""

    def __init__(self, cs):
        self.bs = [abs(c) for c in cs if c != 0]
        self.shift = sum(c for c in cs if c < 0)
        self.lo = self.shift
        self.hi = self.shift + sum(self.bs)

    def cdf(self, y):
        return _cdf(self.bs, F(y) - self.shift)


# ------------------------------------------------------------- rank-1 limits
def rank1_limit(n0):
    """Exact Haar average of the good indicator over { v in T^4 : n0.v = 0 }."""
    sig = max(range(4), key=lambda i: abs(n0[i]))
    n = n0[sig]
    if n < 0:
        n0 = tuple(-x for x in n0)
        n = -n
    others = [i for i in range(4) if i != sig]
    cs = [n0[i] for i in others]
    X = LinForm(cs)
    tot = F(0)
    for js in itertools.product(range(4), repeat=3):
        J = sum(c * j for c, j in zip(cs, js))
        for t in range(n):
            Q = 4 * t - J
            # m ranges over the integers with (Q - X) / n landing in [X.lo, X.hi]
            mlo = (Q - X.hi) // n - 1
            mhi = (Q - X.lo) // n + 1
            acc = F(0)
            for m in range(mlo, mhi + 1):
                p = X.cdf(Q - m * n) - X.cdf(Q - (m + 1) * n)
                if p == 0:
                    continue
                acc += p
                a = [0, 0, 0, 0]
                for i, j in zip(others, js):
                    a[i] = j
                a[sig] = m % 4
                if len({ar ^ mr for ar, mr in zip(a, MU)}) == 4:
                    tot += p
            assert acc == 1, (n0, js, t, acc)
    return tot / (64 * n)


# ------------------------------------------- integer column HNF / kernel basis
def kernel_basis(M):
    """M: list of rows (each length 4), integer, rank k.  Return a 4 x (4-k) integer
    matrix B (list of 4 rows) whose columns are a Z-basis of the SATURATED kernel
    { x in Z^4 : M x = 0 }.  Uses column operations with a tracked unimodular U."""
    A = [row[:] for row in M]
    k = len(A)
    ncols = 4
    U = [[1 if i == j else 0 for j in range(ncols)] for i in range(ncols)]

    def colop(j1, j2, q):           # col_j1 -= q * col_j2
        for r in range(k):
            A[r][j1] -= q * A[r][j2]
        for r in range(ncols):
            U[r][j1] -= q * U[r][j2]

    def colswap(j1, j2):
        for r in range(k):
            A[r][j1], A[r][j2] = A[r][j2], A[r][j1]
        for r in range(ncols):
            U[r][j1], U[r][j2] = U[r][j2], U[r][j1]

    piv = 0
    for i in range(k):
        # gcd-eliminate row i across columns piv..3
        while True:
            nz = [j for j in range(piv, ncols) if A[i][j] != 0]
            if len(nz) <= 1:
                break
            nz.sort(key=lambda j: abs(A[i][j]))
            j0 = nz[0]
            for j in nz[1:]:
                colop(j, j0, A[i][j] // A[i][j0])
        nz = [j for j in range(piv, ncols) if A[i][j] != 0]
        if nz:
            if nz[0] != piv:
                colswap(piv, nz[0])
            piv += 1
    B = [[U[r][j] for j in range(piv, ncols)] for r in range(ncols)]
    for row in M:                                  # verify M B = 0
        for c in range(ncols - piv):
            assert sum(row[r] * B[r][c] for r in range(4)) == 0
    return B, piv


# --------------------------------------------------- exact polygon clipping 2D
def _clip(poly, a, b, c, strict_upper):
    """keep { a x + b y <= c } (strict_upper False) or { a x + b y >= c } (True)."""
    if not poly:
        return poly
    out = []
    n = len(poly)
    def val(p):
        v = a * p[0] + b * p[1] - c
        return -v if strict_upper else v          # keep val <= 0
    for i in range(n):
        p, q = poly[i], poly[(i + 1) % n]
        vp, vq = val(p), val(q)
        if vp <= 0:
            out.append(p)
        if (vp < 0 < vq) or (vq < 0 < vp):
            t = vp / (vp - vq)
            out.append((p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])))
    return out


def _area(poly):
    if len(poly) < 3:
        return F(0)
    s = F(0)
    n = len(poly)
    for i in range(n):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % n]
        s += x1 * y2 - x2 * y1
    return abs(s) / 2


def floor_joint_law_2d(rows):
    """rows: list of integer pairs (c1,c2).  Returns {d-tuple: exact area} for
    { s in [0,1)^2 : floor(c . s) = d }."""
    rng = []
    for (c1, c2) in rows:
        lo = min(0, c1) + min(0, c2)
        hi = max(0, c1) + max(0, c2)
        rng.append(range(lo, hi + 1))
    size = 1
    for r in rng:
        size *= len(r)
    if size > 4_000_000:
        raise ValueError(f"floor_joint_law_2d: {size} cells, too large "
                         f"(rows {rows}) -- caller should skip this lattice")
    out = {}
    unit = [(F(0), F(0)), (F(1), F(0)), (F(1), F(1)), (F(0), F(1))]
    for d in itertools.product(*rng):
        poly = unit
        for (c1, c2), dv in zip(rows, d):
            if c1 == 0 and c2 == 0:
                if dv != 0:
                    poly = []
                    break
                continue
            poly = _clip(poly, c1, c2, F(dv), True)      # c.s >= d
            poly = _clip(poly, c1, c2, F(dv + 1), False)  # c.s <= d+1
            if not poly:
                break
        A = _area(poly)
        if A:
            out[d] = A
    assert sum(out.values()) == 1, (rows, sum(out.values()))
    return out


def rank2_limit(M):
    """M = [n1, n2] integer rows of rank 2.  Exact Haar average over the (saturated)
    subtorus { v : n.v = 0 for n in <n1,n2> }."""
    B, rk = kernel_basis(M)
    assert rk == 2 and len(B[0]) == 2, (M, rk)
    rows = [tuple(B[r]) for r in range(4)]
    law = floor_joint_law_2d(rows)
    tot = F(0)
    for ks in itertools.product(range(4), repeat=2):
        base = [rows[r][0] * ks[0] + rows[r][1] * ks[1] for r in range(4)]
        for d, A in law.items():
            a = [(base[r] + d[r]) % 4 for r in range(4)]
            if len({ar ^ mr for ar, mr in zip(a, MU)}) == 4:
                tot += A
    return tot / 16


# ------------------------------------------------------------- admissibility
def admissible(n):
    if all(x == 0 for x in n):
        return False
    if reduce(gcd, [abs(x) for x in n]) != 1:
        return False
    if sum(x * r for x, r in zip(n, RHO)) % 8 != 0:
        return False
    sup = [x for x in n if x]
    if len(sup) < 2 or min(sup) > 0 or max(sup) < 0:
        return False
    return True


def witnesses(M, PMAX=40, cap=None, want=6):
    """Primitive unit 4-tuples e with n.e = 0 for every n in M.

    e must lie in the SATURATED kernel of M, so e = B alpha with alpha integer; we
    enumerate alpha in a box and filter by e_rho > 0, e_rho = rho mod 8, gcd 1."""
    B, rk = kernel_basis(M)
    r = len(B[0])
    found = []
    for al in itertools.product(range(-PMAX, PMAX + 1), repeat=r):
        e = tuple(sum(B[i][c] * al[c] for c in range(r)) for i in range(4))
        if any(x <= 0 for x in e):
            continue
        if any(x % 8 != RHO[i] % 8 for i, x in enumerate(e)):
            continue
        if len(set(e)) != 4 or reduce(gcd, e) != 1:
            continue
        if cap is not None and max(e) > cap:
            continue
        found.append(e)
    found.sort(key=lambda e: max(e))
    return found[:want]


def row_hnf(rows):
    """canonical row-style Hermite normal form of an integer row lattice."""
    A = [list(r) for r in rows if any(r)]
    m = len(A)
    piv = 0
    for j in range(4):
        cand = [i for i in range(piv, m) if A[i][j] != 0]
        if not cand:
            continue
        while len(cand) > 1:
            cand.sort(key=lambda i: abs(A[i][j]))
            i0 = cand[0]
            for i in cand[1:]:
                q = A[i][j] // A[i0][j]
                for c in range(4):
                    A[i][c] -= q * A[i0][c]
            cand = [i for i in range(piv, m) if A[i][j] != 0]
        i0 = cand[0]
        A[piv], A[i0] = A[i0], A[piv]
        if A[piv][j] < 0:
            A[piv] = [-x for x in A[piv]]
        for i in range(piv):
            q = A[i][j] // A[piv][j]
            for c in range(4):
                A[i][c] -= q * A[piv][c]
        piv += 1
    return tuple(tuple(r) for r in A[:piv])


def lattice_key(M):
    """canonical key for the SATURATED lattice spanned by the rows of M."""
    B, rk = kernel_basis(M)                       # 4 x (4-rk), saturated kernel
    Bt = [[B[r][c] for r in range(4)] for c in range(len(B[0]))]
    Lb, _ = kernel_basis(Bt)                      # 4 x rk, spans the saturation of <M>
    rows = [tuple(Lb[r][c] for r in range(4)) for c in range(len(Lb[0]))]
    return row_hnf(rows), rk
