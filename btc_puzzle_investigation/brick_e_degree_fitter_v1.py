#!/usr/bin/env python3
"""
Brick E — exact minimal-polynomial-degree fitter (the statistic engine, Q2/Q3 of
PREREG_brick_e_cd_degree_v1.md). GATE-INDEPENDENT MECHANICAL CORE ONLY.

This file computes NOTHING about the real c(d) signal. It provides:
  min_degree_fit(points, M) -> smallest D with an exact polynomial fit mod M, or None
  invert_fit(coeffs, target, M, n) -> the d in [0,n) solving the poly = target, if unique

Exact integer arithmetic only (no float, no true division in the signal path).
Fitting mod a composite M is done by CRT over prime-power factors; per factor the
Vandermonde system is solved over Z/q^e by Hensel lifting a solution mod q.

Validated below on SYNTHETIC PLANTED data (the firing control, Q5-i) — planted data
is not the real signal, so running this pre-registration-freeze is legitimate.
"""

def factorize(M):
    """Exact trial-division factorization -> {prime: exponent}. M small (group order)."""
    f, d = {}, 2
    while d * d <= M:
        while M % d == 0:
            f[d] = f.get(d, 0) + 1
            M //= d
        d += 1 if d == 2 else 2
    if M > 1:
        f[M] = f.get(M, 0) + 1
    return f


def _inv_mod_prime(a, q):
    """Inverse of a mod prime q via Fermat; a not divisible by q."""
    return pow(a % q, q - 2, q)


def _solve_linear_mod_prime(A, b, q):
    """Gaussian elimination of A x = b over the field Z/q (q prime).
    A: list of rows (lists); returns a particular solution list, or None if inconsistent.
    Assumes the system has a solution when the Vandermonde columns are independent."""
    m, ncol = len(A), len(A[0])
    A = [row[:] + [b[i] % q] for i, row in enumerate(A)]
    piv_col = []
    r = 0
    for c in range(ncol):
        piv = next((i for i in range(r, m) if A[i][c] % q != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        invp = _inv_mod_prime(A[r][c], q)
        A[r] = [(x * invp) % q for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] % q != 0:
                f = A[i][c] % q
                A[i] = [(A[i][j] - f * A[r][j]) % q for j in range(ncol + 1)]
        piv_col.append(c)
        r += 1
        if r == m:
            break
    for i in range(r, m):
        if A[i][ncol] % q != 0:
            return None  # inconsistent
    x = [0] * ncol
    for i, c in enumerate(piv_col):
        x[c] = A[i][ncol] % q
    return x


def _fit_degree_mod_prime_power(ds, cs, D, q, e):
    """Exact fit c(d)=sum_{i<=D} a_i d^i (mod q^e) via Hensel lift of a mod-q solution.
    Returns coeffs list length D+1 mod q^e, or None if no exact fit of degree <= D."""
    qe = q ** e
    # Solve mod q first.
    Vq = [[pow(d % q, i, q) for i in range(D + 1)] for d in ds]
    a = _solve_linear_mod_prime(Vq, [c % q for c in cs], q)
    if a is None:
        return None
    # Verify the mod-q solution actually fits every point mod q (overdetermined check).
    for d, c in zip(ds, cs):
        if sum(a[i] * pow(d, i, q) for i in range(D + 1)) % q != c % q:
            return None
    # Hensel-lift the coefficient vector level by level: a_{k+1} = a_k + q^k * t.
    mod = q
    for _ in range(1, e):
        newmod = mod * q
        # residual r = (c - poly(a)) / mod   must be integer mod q; solve V t = r mod q
        res = []
        for d, c in zip(ds, cs):
            val = sum(a[i] * pow(d, i, newmod) for i in range(D + 1)) % newmod
            diff = (c - val) % newmod
            if diff % mod != 0:
                return None
            res.append((diff // mod) % q)
        Vq = [[pow(d % q, i, q) for i in range(D + 1)] for d in ds]
        t = _solve_linear_mod_prime(Vq, res, q)
        if t is None:
            return None
        a = [(a[i] + mod * t[i]) % newmod for i in range(D + 1)]
        mod = newmod
    # Final exact check mod q^e.
    for d, c in zip(ds, cs):
        if sum(a[i] * pow(d, i, qe) for i in range(D + 1)) % qe != c % qe:
            return None
    return a


def _crt_pair(a1, m1, a2, m2):
    """CRT combine (a1 mod m1, a2 mod m2) with gcd(m1,m2)=1 -> (a, m1*m2)."""
    # extended gcd
    g, x, y = m1, 1, 0
    a, b = m1, m2
    x0, x1 = 1, 0
    while b:
        qy = a // b
        a, b = b, a - qy * b
        x0, x1 = x1, x0 - qy * x1
    inv = x0 % m2  # inverse of m1 mod m2
    t = ((a2 - a1) * inv) % m2
    return (a1 + m1 * t) % (m1 * m2), m1 * m2


def fit_degree_mod_M(ds, cs, D, M):
    """Exact degree-<=D fit mod composite M via CRT over prime-power factors.
    Returns coeffs mod M (length D+1) or None."""
    coeffs_mod, mod = [0] * (D + 1), 1
    for q, e in factorize(M).items():
        a = _fit_degree_mod_prime_power(ds, cs, D, q, e)
        if a is None:
            return None
        qe = q ** e
        coeffs_mod = [_crt_pair(coeffs_mod[i], mod, a[i], qe)[0] for i in range(D + 1)]
        mod *= qe
    return coeffs_mod


def min_degree_fit(points, M, Dmax=None):
    """Smallest D such that the points {d: c(d)} admit an exact poly fit mod M.
    points: dict d->c. Returns (D, coeffs) or (None, None) if none up to Dmax."""
    ds = sorted(points)
    cs = [points[d] for d in ds]
    if Dmax is None:
        Dmax = len(ds) - 1
    for D in range(0, Dmax + 1):
        a = fit_degree_mod_M(ds, cs, D, M)
        if a is not None:
            return D, a
    return None, None


def invert_fit(coeffs, target, M, n):
    """Brute d in [0,n): which d give poly(d) == target mod M. n small (model scale)."""
    D = len(coeffs) - 1
    return [d for d in range(n)
            if sum(coeffs[i] * pow(d, i, M) for i in range(D + 1)) % M == target % M]


# ---------------------------------------------------------------------------
# UNIT TEST on SYNTHETIC PLANTED data (Q5-i firing control) — NOT the real signal.
# ---------------------------------------------------------------------------
if __name__ == "__main__":
    import random
    M = 1893          # = 3 * 631, the p=43 A_new-part order (composite, exercises CRT)
    n = 31            # |E(F_43)|
    random.seed(20260820)

    # (1) Planted degree-2, no linear term (respects F1): c*(d) = a2 d^2 + a0.
    a2, a0 = 777, 123
    planted = {d: (a2 * d * d + a0) % M for d in range(n)}
    D, coeffs = min_degree_fit(planted, M)
    print(f"[plant deg-2] recovered D = {D}  (expect 2)   coeffs = {coeffs}")
    assert D == 2 and coeffs[1] % M == 0, "engine failed to recover planted degree-2 / linear term"

    # inversion: pick a target, confirm we recover the planted d
    d_true = 19
    tgt = planted[d_true]
    roots = invert_fit(coeffs, tgt, M, n)
    print(f"[plant deg-2] invert target c({d_true}) -> d in {roots}  (expect contains {d_true})")
    assert d_true in roots, "inversion did not recover planted d"

    # (2) Planted degree-3 to confirm the ladder climbs correctly.
    a3, a1, a0b = 55, 400, 9
    p3 = {d: (a3 * d**3 + a1 * d + a0b) % M for d in range(n)}
    D3, _ = min_degree_fit(p3, M)
    print(f"[plant deg-3] recovered D = {D3}  (expect 3)")
    assert D3 == 3

    # (3) Random map (matched-null SANITY on the ENGINE only): should need high degree.
    #     This is engine validation, NOT the real signal and NOT the registered null (Q4).
    rnd = {d: random.randrange(M) for d in range(n)}
    Dr, _ = min_degree_fit(rnd, M)
    # D=None is the STRONGEST "not low-degree": no exact poly fit exists mod M at any degree.
    # (Mod the small factor 3, d^3==d collapses polys to functions of d mod 3, so a random map
    #  usually admits no fit at all mod 3 -> None. The degree statistic is therefore meaningful
    #  mod the LARGE prime factor(s); see DEVIATIONS note. This is a per-CRT-factor phenomenon.)
    print(f"[random map] recovered D = {Dr}  (expect None or high, ~n-1={n-1})")
    assert Dr is None or Dr >= n // 2, "random map fit too low — engine would give false positives"

    # (3b) Per-large-factor degree on the random map: mod 631 (all d distinct), the fit exists
    #      but at high degree — this is the branch the real statistic reads.
    Dr631, _ = min_degree_fit(rnd, 631)
    print(f"[random map mod 631] recovered D = {Dr631}  (expect high, engine has no false low-D)")
    assert Dr631 is None or Dr631 >= n // 2

    # (4) CRT correctness cross-check: fit mod 3 and mod 631 separately, recombine, compare.
    D4, c4 = min_degree_fit(planted, M)
    ok = all((c4[i] % 3, c4[i] % 631) == ((a2 if i == 2 else a0 if i == 0 else 0) % 3,
                                          (a2 if i == 2 else a0 if i == 0 else 0) % 631)
             for i in range(D4 + 1))
    print(f"[CRT check] per-factor residues match planted coeffs: {ok}")
    assert ok

    print("\nALL ENGINE UNIT TESTS PASSED — mechanical core (Q2/Q3) validated on planted data.")
