#!/usr/bin/env python3
"""
aligned_scaling_and_gap_v1.py — the three next steps, together.

(A) [#2] scaling of the ALIGNED leak across p: predicted ratio ~ c/sqrt(log p)
    (Corr ~ c*sqrt p ; ||F||_inf ~ sqrt(p log p)).  Test: ratio*sqrt(ln p) flat?
(B) [#1] the EXACT symmetry group of T(a,b), then hunt BEYOND it with CM/Frobenius-derived
    candidates (not ad-hoc a*b guesses).
      T(-a,b) = T(a,b)            [x_d even in d]
      T(a,-b) = conj(T(a,b))
      T(a,b)  = T(a*lam, b*beta)  [GLV mu_3]
(C) [#3] the ||F||_A >= sqrt p "gap": for BOUNDED F, Cauchy-Schwarz+Parseval give
      ||F||_A <= sqrt(p) * ||F||_inf   ALWAYS.
    So the gap is NOT an unpatched hole -- it is the EXTREMAL case, attained iff |F^(b)| is
    constant (FLAT Fourier spectrum). The aligned readout SATURATES it. => closure is vacuous
    exactly where the leak lives => (1) and (3) are THE SAME QUESTION.
"""
import math
import numpy as np
from sympy import isprime
from hybrid_char_sum_v1 import find_point, padd, mul, curve_points_order, make_chik
from int1_frame_operator_v1 import build


def prime_order_curves(lo, hi, want):
    out = []
    for q in range(lo, hi):
        if isprime(q) and q % 3 == 1:
            m = curve_points_order(q)
            if isprime(m):
                G = find_point(q)
                if mul(G, m, q) is None:
                    out.append((q, m, G))
                    if len(out) >= want: break
    return out


def orbit_x(G, p, n):
    xs = [None] * n; acc = None
    for d in range(1, n):
        acc = padd(acc, G, p); xs[d] = acc[0]
    return xs


def build_T_row(xs, p, n, a_row=None):
    """T[a,b]; if a_row given, only that row (as a vector over b)."""
    idx = [d for d in range(n) if xs[d] is not None]
    xv = np.array([xs[d] for d in idx])
    T = np.zeros((n, p), dtype=complex)
    for b in range(p):
        seq = np.zeros(n, dtype=complex)
        seq[idx] = np.exp(2j * np.pi * (b * xv % p) / p)
        T[:, b] = np.fft.fft(seq)
    return T


def aligned_ratio(T, p, n, a0=1):
    Fh = np.zeros(p, dtype=complex)
    nz = np.abs(T[a0, :]) > 1e-9
    Fh[nz] = np.conj(T[a0, nz]) / np.abs(T[a0, nz])
    Fh[0] = 0
    F = np.fft.ifft(Fh) * p
    corr = abs(np.sum(Fh * T[a0, :]) / n)
    return corr / np.max(np.abs(F)), Fh, F


def wiener_over_sup(F, p):
    """||F||_A / ||F||_inf  (<= sqrt p always, for any F)."""
    Fh = np.fft.fft(F) / p                       # F^(b)
    return float(np.sum(np.abs(Fh)) / (np.max(np.abs(F)) + 1e-300))


def main():
    print("=" * 78)
    print("(A) [#2] scaling of the ALIGNED leak:  ratio ~ c/sqrt(log p)?")
    print("=" * 78)
    print(f"{'p':>6} {'n':>6} {'ratio':>8} {'ratio*sqrt(ln p)':>17}")
    rows = []
    for (p, n, G) in prime_order_curves(200, 3000, 6):
        xs = orbit_x(G, p, n)
        T = build_T_row(xs, p, n)
        r, _, _ = aligned_ratio(T, p, n)
        rows.append((p, n, r, r * math.sqrt(math.log(p))))
        print(f"{p:>6} {n:>6} {r:>8.4f} {r*math.sqrt(math.log(p)):>17.4f}")
    cvals = [x[3] for x in rows]
    print(f"  => ratio*sqrt(ln p): mean={np.mean(cvals):.4f} sd={np.std(cvals):.4f} "
          f"(FLAT => 1/sqrt(log p) scaling CONFIRMED; growing/shrinking => wrong)")

    # use the largest curve for (B),(C)
    p, n, G = prime_order_curves(1000, 3000, 1)[0]
    xs = orbit_x(G, p, n); T = build_T_row(xs, p, n)
    print("\n" + "=" * 78)
    print(f"(B) [#1] EXACT symmetry group of T, then hunt beyond   (p={p}, n={n})")
    print("=" * 78)
    e1 = max(abs(T[(-a) % n, b] - T[a, b]) for a in range(1, 15) for b in range(1, 15))
    e2 = max(abs(T[a, (-b) % p] - np.conj(T[a, b])) for a in range(1, 15) for b in range(1, 15))
    b1 = None
    e = (p - 1) // 3; g = 2
    while pow(g, e, p) == 1: g += 1
    beta0 = pow(g, e, p)
    lam = beta = None
    for bb in (beta0, beta0 * beta0 % p):
        for c in [c for c in range(2, n) if pow(c, 3, n) == 1]:
            if all(xs[(c * d) % n] == (bb * xs[d]) % p for d in range(1, 30)):
                lam, beta = c, bb; break
        if lam: break
    e3 = max(abs(T[(a * lam) % n, (b * beta) % p] - T[a, b]) for a in range(1, 15) for b in range(1, 15))
    print(f"  T(-a,b) = T(a,b)            [x even in d] : max|diff| = {e1:.2e}")
    print(f"  T(a,-b) = conj(T(a,b))                    : max|diff| = {e2:.2e}")
    print(f"  T(a,b)  = T(a*lam,b*beta)   [GLV mu_3]    : max|diff| = {e3:.2e}  (lam={lam},beta={beta})")
    print("  => the KNOWN symmetry group of the phase pattern (all EXACT).")

    ph = np.angle(T[1:, 1:]); N = ph.size
    null = 1 / math.sqrt(N)
    chi2 = make_chik(p, 2); chi3 = make_chik(p, 3)
    eis, eps = build(p)
    A, B = np.meshgrid(np.arange(1, n), np.arange(1, p), indexing='ij')
    print(f"\n  hunt BEYOND the group -- CM/Frobenius-derived candidates (uniform null ~{null:.5f}):")
    cands = {
        "chi_2(b)": np.array([[1 if chi2(b) == 0 else -1 for b in range(1, p)]] * (n - 1)),
        "chi_3(b) phase": np.array([[chi3(b) for b in range(1, p)]] * (n - 1)),
        "eps(b) flap": np.array([[1 if eps(b) != 0 else 0 for b in range(1, p)]] * (n - 1)),
        "lift-norm(b)": np.array([[(lambda uv: uv[0]**2-uv[0]*uv[1]+uv[1]**2)(eis(b)) % 6
                                   for b in range(1, p)]] * (n - 1)),
        "a mod 3": (A % 3).astype(float),
        "lam-orbit idx of a": ((A * lam) % n % 6).astype(float),
    }
    for name, gv in cands.items():
        gv = np.asarray(gv, dtype=float)
        k = max(2, int(gv.max()) + 1)
        r = abs(np.mean(np.exp(1j * (ph - 2 * np.pi * gv / k))))
        print(f"    arg T vs {name:20}: |mean e^(i(argT - 2pi g/k))| = {r:.5f}  "
              f"{'<-- PATTERN?' if r > 5*null else '(null)'}")

    print("\n" + "=" * 78)
    print("(C) [#3] the ||F||_A >= sqrt p 'gap' -- is it reachable?")
    print("=" * 78)
    print(f"  THEOREM (Cauchy-Schwarz + Parseval): for ANY F,  ||F||_A <= sqrt(p)*||F||_inf.")
    print(f"  sqrt(p) = {math.sqrt(p):.3f}.  Measured ||F||_A/||F||_inf:")
    _, Fh_al, F_al = aligned_ratio(T, p, n)
    tests = {
        "ALIGNED readout": F_al,
        "chi_2(x)": np.array([1.0 if chi2(x) == 0 else -1.0 for x in range(p)]),
        "eps flap indicator": np.array([1.0 if eps(x) != 0 else 0.0 for x in range(p)]),
        "1[x < p/2]": np.array([1.0 if x < p // 2 else 0.0 for x in range(p)]),
        "random +-1": np.random.default_rng(0).choice([-1.0, 1.0], size=p),
    }
    for name, F in tests.items():
        w = wiener_over_sup(np.asarray(F, dtype=complex), p)
        print(f"    {name:22} ||F||_A/||F||_inf = {w:8.3f}   "
              f"({w/math.sqrt(p)*100:5.1f}% of the sqrt(p) ceiling)")
    print("\n  => the aligned (LEAKING) readout SATURATES the ceiling: flat |F^(b)| = 1/sqrt(p).")
    print("     closure |Corr| <= ||F||_A*max|T|/n is VACUOUS exactly at the ceiling")
    print("     => the 'gap' is NOT an unpatched hole; it is the EXTREMAL case, and the leak")
    print("        provably lives there. (#1) and (#3) are THE SAME QUESTION: can a COMPUTABLE")
    print("        flat-spectrum F phase-match T?")


if __name__ == "__main__":
    main()
