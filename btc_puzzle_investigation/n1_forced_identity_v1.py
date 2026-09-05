#!/usr/bin/env python3
"""
n1_forced_identity_v1.py -- the INDEPENDENT adjudication check for the N1 `v <= 0` question.

WHY THIS EXISTS.  AUDIT_prereg_n1_v_sign_sweep_v2_v1.md check 9 (B4) establishes that the F5
adjudication gate has ZERO discriminating power over the frozen scope: every clause either re-runs an
exact computation, tests a FORCED identity that cannot fail on correct data, or (clause c) cannot run
at all because the scope starts at p=127 > 61.  So a `v > 0` cell passes adjudication automatically.
The same audit then produced `v > 0` cells at p = 127, 163, 211.

This script supplies the missing discriminating check.  It computes V_3 -- which the `v <= 0`
pipeline never touches -- and tests the FORCED identity

        e3 = -p * e1     (SIN, p = 3 mod 4)        e3 = +p * e1   (COS, p = 1 mod 4)

as an exact integer-vector identity in Z[x]/Phi_n.  Because

        e3 = (-V1^3 - 3*V1*V2 - 2*V3)/6

CONTAINS V2, and V2 is exactly what `e2 = (V1^2 + V2)/2` -- hence `v` -- is built from, a bug in V2
generically breaks e3 = -p*e1.  The identity is forced by the weight/functional-equation structure and
is INDEPENDENT of the `v <= 0` question: it constrains V1,V2,V3 jointly and says nothing about the
sign of v.  That is what makes it a discriminating gate rather than a restatement.

  * V_1, V_2 come from audit_n1_vsign_v2_core.py (independent implementation, validated exactly
    against the frozen p=13 and p=43 references in check 1 of the audit).
  * V_3 is computed HERE by a third, vectorized implementation over F_{p^3} = F_p[x]/(x^3 - c),
    which is a different field model, a different Frobenius, and a different code path.

EXACTNESS.  The signal path is integer-only: numpy int64 modular arithmetic (all intermediates bounded
by ~4.1e6 << 2^63 at p <= 211) and Python int for the polynomial algebra.  No float anywhere.
"""
import sys, time
import numpy as np

sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_core import (is_prime, legendre, curve_order, dlog_table,
                                    hist_k1, hist_k2, reduce_phi_prime)

B = 7


# ---------------------------------------------------------------- exact poly algebra mod Phi_n
def mulF(A, B_, n):
    """product in Z[x]/Phi_n, inputs/outputs length n-1 integer vectors."""
    C = [0] * (2 * n)
    for i, ai in enumerate(A):
        if ai:
            for j, bj in enumerate(B_):
                if bj:
                    C[i + j] += ai * bj
    D = [0] * n
    for i, ci in enumerate(C):
        D[i % n] += ci
    return reduce_phi_prime(D, n)


def red(h, n):
    return reduce_phi_prime(list(h), n)


# ---------------------------------------------------------------- vectorized F_{p^3}
class F3vec:
    """F_{p^3} = F_p[x]/(x^3 - c), c a non-cube.  Requires p = 1 mod 3 (forced for this curve)."""

    def __init__(self, p):
        assert p % 3 == 1, "p = 1 mod 3 is forced by #E prime; non-cubes need it"
        self.p = p
        e = (p - 1) // 3
        c = 2
        while pow(c, e, p) == 1:          # c is a cube iff c^((p-1)/3) == 1
            c += 1
        self.c = c
        self.w = pow(c, e, p)             # x^p = c^((p-1)/3) * x
        assert pow(self.w, 3, p) == 1 and self.w != 1
        self.N = p ** 3

    def mul(self, A, Bv):
        p, c = self.p, self.c
        a0, a1, a2 = A[:, 0], A[:, 1], A[:, 2]
        b0, b1, b2 = Bv[:, 0], Bv[:, 1], Bv[:, 2]
        return np.stack([(a0 * b0 + c * (a1 * b2 + a2 * b1)) % p,
                         (a0 * b1 + a1 * b0 + c * (a2 * b2)) % p,
                         (a0 * b2 + a1 * b1 + a2 * b0) % p], axis=1)

    def sub(self, A, Bv):
        return (A - Bv) % self.p

    def neg(self, A):
        return (-A) % self.p

    def enc(self, A):
        p = self.p
        return A[:, 0] + p * A[:, 1] + p * p * A[:, 2]

    def dec(self, e):
        p = self.p
        return np.stack([e % p, (e // p) % p, e // (p * p)], axis=1)

    def frob(self, A):
        """x -> x^p is DIAGONAL in this model: (a0,a1,a2) -> (a0, w*a1, w^2*a2)."""
        p, w = self.p, self.w
        return np.stack([A[:, 0], (A[:, 1] * w) % p, (A[:, 2] * (w * w % p)) % p], axis=1)

    def inv(self, A):
        """a^(q-2), vectorized square-and-multiply.  A must have no zero rows."""
        e = self.N - 2
        R = np.zeros_like(A); R[:, 0] = 1
        Bb = A.copy()
        while e:
            if e & 1:
                R = self.mul(R, Bb)
            Bb = self.mul(Bb, Bb)
            e >>= 1
        return R

    def is_zero(self, A):
        return (A[:, 0] == 0) & (A[:, 1] == 0) & (A[:, 2] == 0)


def ec_add_vec(F, X1, Y1, inf1, X2, Y2, inf2):
    """
    Vectorized addition on y^2 = x^3 + B over F_{p^3}.  Returns (X3, Y3, inf3).
    Handles infinity, P = -Q, and doubling by masks.
    """
    p = F.p
    same_x = F.is_zero(F.sub(X1, X2))
    opp_y = F.is_zero((Y1 + Y2) % p)
    is_dbl = same_x & (~opp_y)
    to_inf = same_x & opp_y

    # NB: 3*x1^2 is SCALAR multiplication by 3, not multiplication by the element (3,3,3).
    num = np.where(is_dbl[:, None], (3 * F.mul(X1, X1)) % p, F.sub(Y2, Y1))
    den = np.where(is_dbl[:, None], (2 * Y1) % p, F.sub(X2, X1))

    # protect the inversion on rows we will discard anyway
    bad = F.is_zero(den)
    den_safe = den.copy()
    den_safe[bad, 0] = 1
    den_safe[bad, 1] = 0
    den_safe[bad, 2] = 0

    lam = F.mul(num, F.inv(den_safe))
    X3 = F.sub(F.sub(F.mul(lam, lam), X1), X2)
    Y3 = F.sub(F.mul(lam, F.sub(X1, X3)), Y1)
    inf3 = to_inf.copy()

    # P at infinity -> result is Q ; Q at infinity -> result is P
    X3 = np.where(inf1[:, None], X2, X3); Y3 = np.where(inf1[:, None], Y2, Y3)
    inf3 = np.where(inf1, inf2, inf3)
    X3 = np.where(inf2[:, None], X1, X3); Y3 = np.where(inf2[:, None], Y1, Y3)
    inf3 = np.where(inf2, inf1, inf3)
    return X3, Y3, inf3


def hist_k3(p, n, dl, verbose=True):
    """h3[d] = sum over P in E(F_{p^3}) with Tr(P) = [d]G of chi2^{(3)}(y_P).  Vectorized."""
    t0 = time.time()
    F = F3vec(p)
    N = F.N
    idx = np.arange(N, dtype=np.int64)
    T = F.dec(idx)

    # squares of F_{p^3}: membership (= chi2) and one square root each
    SQ = F.mul(T, T)
    encSQ = F.enc(SQ)
    issq = np.zeros(N, dtype=bool)
    issq[encSQ] = True
    root = np.full(N, -1, dtype=np.int64)
    root[encSQ] = idx
    if verbose:
        print(f"    squares table built ({time.time()-t0:.1f}s)", flush=True)

    # r = x^3 + B
    R = F.mul(F.mul(T, T), T)
    R[:, 0] = (R[:, 0] + B) % p
    encR = F.enc(R)
    ok = (encR != 0) & issq[encR]
    xs = T[ok]
    ys = F.dec(root[encR[ok]])

    h = [0] * n
    # lookup array for E(F_p) discrete logs
    dlarr = np.full(p * p, -1, dtype=np.int64)
    for pt, d in dl.items():
        if pt is not None:
            dlarr[pt[0] * p + pt[1]] = d
    d_inf = dl[None]

    for sign in (0, 1):
        Y = ys if sign == 0 else F.neg(ys)
        chi = np.where(issq[F.enc(Y)], 1, -1)
        X = xs
        inf = np.zeros(len(X), dtype=bool)
        # Tr(P) = P + phi(P) + phi^2(P)
        X1, Y1 = F.frob(X), F.frob(Y)
        X2, Y2 = F.frob(X1), F.frob(Y1)
        Xa, Ya, infa = ec_add_vec(F, X, Y, inf, X1, Y1, inf)
        Xb, Yb, infb = ec_add_vec(F, Xa, Ya, infa, X2, Y2, inf)
        # the trace must land in E(F_p)
        assert not np.any(Xb[~infb, 1:]), "trace not in F_p (x)"
        assert not np.any(Yb[~infb, 1:]), "trace not in F_p (y)"
        dvals = np.where(infb, d_inf, dlarr[Xb[:, 0] * p + Yb[:, 0]])
        assert np.all(dvals >= 0), "dlog lookup failed"
        cnt = np.bincount(dvals, weights=chi, minlength=n)
        for d in range(n):
            h[d] += int(round(cnt[d]))
        if verbose:
            print(f"    y-sign {sign}: {len(X)} points ({time.time()-t0:.1f}s)", flush=True)
    return h


# ---------------------------------------------------------------- driver
def main():
    p = int(sys.argv[1])
    n = curve_order(p, B)
    assert is_prime(n), f"#E = {n} not prime"
    stratum = "SIN (p=3 mod 4)" if p % 4 == 3 else "COS (p=1 mod 4)"
    print(f"p={p}  n=#E={n}  (n-1)/6={(n-1)//6}  {stratum}")

    dl = dlog_table(p, n, B)
    t0 = time.time()
    h1 = hist_k1(p, n, dl, B); print(f"  h1 done ({time.time()-t0:.1f}s)", flush=True)
    t0 = time.time()
    h2 = hist_k2(p, n, dl, B); print(f"  h2 done ({time.time()-t0:.1f}s)", flush=True)
    t0 = time.time()
    h3 = hist_k3(p, n, dl); print(f"  h3 done ({time.time()-t0:.1f}s)", flush=True)

    V1, V2, V3 = red(h1, n), red(h2, n), red(h3, n)

    # F1: e2 = (V1^2 + V2)/2
    W = [a + b for a, b in zip(mulF(V1, V1, n), V2)]
    assert all(x % 2 == 0 for x in W), "e2 not in Z[zeta_n]"
    e2 = [x // 2 for x in W]
    e1 = [-x for x in V1]

    # e3 = (-V1^3 - 3 V1 V2 - 2 V3)/6
    V1_3 = mulF(mulF(V1, V1, n), V1, n)
    V1V2 = mulF(V1, V2, n)
    t = [-a - 3 * b - 2 * c for a, b, c in zip(V1_3, V1V2, V3)]
    assert all(x % 6 == 0 for x in t), "e3 not integral -- V3 is wrong"
    e3 = [x // 6 for x in t]

    want = [(-p if p % 4 == 3 else p) * x for x in e1]
    ok = (e3 == want)
    sgn = '-' if p % 4 == 3 else '+'
    print()
    print(f"  FORCED IDENTITY  e3 = {sgn}p*e1 : {'HOLDS EXACTLY' if ok else '*** FAILS ***'}")
    if not ok:
        diff = [a - b for a, b in zip(e3, want)]
        nz = [(i, d) for i, d in enumerate(diff) if d]
        print(f"    {len(nz)} nonzero components, first few: {nz[:6]}")
    print(f"  e1 (first 8) = {e1[:8]}")
    print(f"  e2 (first 8) = {e2[:8]}")
    print(f"  V3 sum       = {sum(h3)}")
    print()
    print(f"  => V2 is corroborated by a constraint that is independent of the sign of v: "
          f"{'YES' if ok else 'NO'}")


if __name__ == "__main__":
    main()
