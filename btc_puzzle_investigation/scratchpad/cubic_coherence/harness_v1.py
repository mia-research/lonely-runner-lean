#!/usr/bin/env python3
"""
harness_v1.py — exact-integer instrument for the N7-deficit ↔ P18-cubic-coherence test (α).

Data layer only (fixed regardless of the frozen primary statistic):
  * curve_orbit(p): canonical generator + exact [d]G table, d=1..n-1.
  * U_transform(g): U_g(b,c) = Σ_d g(d) e_p(b x_d + c y_d) over ALL (b,c),
        via the analytic-y / FFT-over-x factorization (each x-column holds ≤2 points).
  * hermitian_null(): the EXISTING matched null g(n-d)=conj(g(d)), random phase per ±d pair.
  * cubic_coherence(): the PROVED P18 term  Σ_b χ₂(b) T(a₀,b)³  with T=U_char(·,c=0).
  * exactness anchors: L2 integer identity Σ_{b,c}|U|²=p²(n-1); planted-deficit recovery.

SIGNAL PATH IS EXACT INTEGER.  b*x_d + c*y_d mod p and a0*d mod n are python-int modular.
Float enters ONLY as the unit-modulus root tables e_p[k], zeta_n[k] indexed by EXACT integers,
and in the FFT/moments taken from U — never as a threshold applied to key-derived integers.
(Same carve-out the frozen N7 prereg uses; anchored by the exact L2 identity E1.)

NOTE: this file computes ONLY pre-data-safe quantities (exactness anchors, the PROVED P18
identity, planted controls). The frozen PRIMARY (the character's deficit localization) is added
in run_v1.py AFTER PREREG_subrayleigh_cubic_coherence_v1 is frozen.
"""
import numpy as np
from sympy.ntheory.residue_ntheory import sqrt_mod
from sympy import isprime


# ----------------------------------------------------------------------
# curve + orbit (exact integer)
# ----------------------------------------------------------------------
def curve_orbit(p, B=7):
    """Canonical generator G (minimal (x,y) of order n) and exact [d]G table.
    Returns (n, X, Y) with X[d],Y[d] = coords of [d]G, d=1..n-1 (X[0]=Y[0]=0 sentinel for O)."""
    def add(A, C):
        if A is None: return C
        if C is None: return A
        x1, y1 = A; x2, y2 = C
        if x1 == x2 and (y1 + y2) % p == 0:
            return None
        if x1 == x2:
            lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
        else:
            lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (lam * lam - x1 - x2) % p
        y3 = (lam * (x1 - x3) - y1) % p
        return (x3, y3)

    # order of the group: count points (fine for model p). #E = 1 + Σ_x (1+χ2(x^3+B)) with y=0 handled.
    npts = 1  # O
    for x in range(p):
        r = (x * x * x + B) % p
        if r == 0:
            npts += 1
        elif pow(r, (p - 1) // 2, p) == 1:
            npts += 2
    n = npts
    # canonical generator: minimal (x,y) that generates (order n). n prime here ⇒ any non-O point works,
    # but keep the deterministic minimal rule for reproducibility.
    G = None
    for x in range(p):
        r = (x * x * x + B) % p
        if r and pow(r, (p - 1) // 2, p) == 1:
            y = int(sqrt_mod(r, p))
            for yy in sorted((y, p - y)):
                G = (x, yy)
                break
            break
    if G is None:
        return None
    X = np.zeros(n, dtype=np.int64); Y = np.zeros(n, dtype=np.int64)
    P = None
    for d in range(1, n):
        P = add(P, G)
        if P is None:  # hit identity early ⇒ G not a generator (shouldn't happen for prime n)
            return None
        X[d], Y[d] = P
    return n, X, Y


# ----------------------------------------------------------------------
# root tables (float carve-out, indexed by exact integers)
# ----------------------------------------------------------------------
def root_tables(p, n):
    ep = np.exp(2j * np.pi * np.arange(p) / p)     # e_p[k], k=0..p-1
    en = np.exp(2j * np.pi * np.arange(n) / n)      # zeta_n[k], k=0..n-1
    return ep, en


def char_weight(n, en, a0=1):
    """g(d)=zeta_n^{a0 d}, d=0..n-1 (g(0)=0 excluded from sums by construction)."""
    idx = (a0 * np.arange(n)) % n
    g = en[idx].astype(np.complex128)
    g[0] = 0.0
    return g


# ----------------------------------------------------------------------
# U transform: U_g(b,c) over ALL (b,c), via analytic-y + FFT-over-x
#   U_g(b,c) = Σ_x e_p(b x) [ Σ_{d: x_d=x} g(d) e_p(c y_d) ]
#            = FFT_x of  A(x,c),  A(x,c)=Σ_{d:x_d=x} g(d) e_p(c y_d)
# ----------------------------------------------------------------------
def U_transform(g, X, Y, p, n, ep):
    # group points by x
    # A[c, x] then FFT over x (axis=1) gives U[c, b]; we return U[b, c] for readability.
    A = np.zeros((p, p), dtype=np.complex128)   # A[c, x]
    xs = X[1:]; ys = Y[1:]; gs = g[1:]
    # e_p(c*y) for all c at once is expensive; loop over points, accumulate per (x) with the c-phase.
    # For each point d: contributes g_d * e_p(c*y_d) to A[c, x_d] for all c.
    #   e_p(c*y_d) over c=0..p-1 is ep[(c*y_d) % p] = ep[(arange(p)*y_d) % p].
    for xd, yd, gd in zip(xs.tolist(), ys.tolist(), gs.tolist()):
        cph = ep[(np.arange(p) * yd) % p]        # length-p, exact integer index
        A[:, xd] += gd * cph
    U = np.fft.fft(A, axis=1)                    # U[c, b] = Σ_x A[c,x] e^{-2πi b x/p}? sign convention
    # np.fft uses e^{-2πi b x/p}; we want e_p(b x)=e^{+2πi b x/p}. Use conj-index: U(b,c)=Σ_x A(x,c)e^{+..}
    # = (ifft * p). Use ifft to get the + sign:
    U = np.fft.ifft(A, axis=1) * p               # U[c, b] with e^{+2πi b x/p}
    return U.T.copy()                            # U[b, c]


def M_L1(U):
    return np.abs(U).mean()


def L2_total(U):
    return (np.abs(U) ** 2).sum()


# ----------------------------------------------------------------------
# Hermitian matched null (the EXISTING N7 null)
# ----------------------------------------------------------------------
def hermitian_null(n, seed):
    rng = np.random.default_rng(seed)
    g = np.zeros(n, dtype=np.complex128)
    for d in range(1, n):
        nd = n - d
        if d < nd:
            phi = rng.uniform(0, 2 * np.pi)
            g[d] = np.exp(1j * phi)
            g[nd] = np.exp(-1j * phi)
        elif d == nd:  # n even, 2-torsion
            g[d] = rng.choice([1.0, -1.0])
    return g


# ----------------------------------------------------------------------
# P18 proved cubic coherence:  Σ_b χ₂(b) T(a0,b)^3,  T(a0,b)=U_char(b, c=0)
# ----------------------------------------------------------------------
def chi2_table(p):
    chi = np.zeros(p, dtype=np.int64)
    for b in range(1, p):
        chi[b] = 1 if pow(b, (p - 1) // 2, p) == 1 else -1
    return chi


def cubic_coherence(U_char, p):
    """Σ_b χ₂(b) T(b)^3 with T(b)=U_char(b, c=0).  Compare to i*√p*(n²-O(n))."""
    T = U_char[:, 0]                              # c=0 slice
    chi = chi2_table(p)
    S = np.sum(chi * (T ** 3))
    return S, T


# ----------------------------------------------------------------------
# instrument self-tests (pre-data-safe: exactness anchors + PROVED P18 + planted control)
# ----------------------------------------------------------------------
def selftest(p, B=7, verbose=True):
    orb = curve_orbit(p, B)
    assert orb is not None, f"no cyclic orbit at p={p}"
    n, X, Y = orb
    ep, en = root_tables(p, n)
    g = char_weight(n, en, a0=1)
    U = U_transform(g, X, Y, p, n, ep)

    # E1: exact L2 integer identity  Σ_{b,c}|U|² = p²(n-1)
    l2 = L2_total(U)
    target = float(p * p * (n - 1))
    relerr = abs(l2 - target) / target

    # P18: Σ_b χ₂(b) T³  vs  i√p(n²-O(n)).  Report ratio Im(S)/(√p n²).
    S, T = cubic_coherence(U, p)
    pred = np.sqrt(p) * n * n
    ratio = S.imag / pred                          # expect ≈ 1 minus O(1/n)

    # Hermitian-null M and a planted deficit recovery (instrument sizing)
    gn = hermitian_null(n, seed=p * 10**6 + 1)
    Un = U_transform(gn, X, Y, p, n, ep)
    Mc = M_L1(U); Mn = M_L1(Un)
    # planted: V = (1-δ)U_null → recovered deficit must equal δ
    delta = 1e-3
    Mpl = M_L1((1 - delta) * Un)
    rec = (Mn - Mpl) / Mn

    if verbose:
        print(f"p={p:6d} n={n:6d} | "
              f"L2 relerr={relerr:.2e} | "
              f"P18 Im(S)/(√p n²)={ratio:+.4f} | "
              f"M_char={Mc:.6f} M_null1={Mn:.6f} | "
              f"planted δ=1e-3 recovered={rec:.3e}")
    return dict(p=p, n=n, l2_relerr=relerr, p18_ratio=ratio, Mc=Mc, Mn1=Mn,
                planted_rec=rec, S=S, pred=pred)


if __name__ == "__main__":
    import sys
    primes = [151, 211, 349, 433, 577]
    if len(sys.argv) > 1:
        primes = [int(a) for a in sys.argv[1:]]
    for p in primes:
        assert isprime(p) and p % 6 == 1, p
        selftest(p)
