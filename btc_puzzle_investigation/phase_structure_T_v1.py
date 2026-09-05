#!/usr/bin/env python3
"""
phase_structure_T_v1.py — the leakage question at the phase level.

Object: the DLP-relevant twisted sum   T(a,b) = sum_d e_p(b*x([d]G)) * e_n(a*d)
(field frequency b x SCALAR frequency a).  Correlation of a readout F with the scalar:
    Corr(a) = (1/n) sum_d F(x_d) e_n(-a d) = (1/n) sum_b F^(b) T(a,b).

DIRECTION 1 (analytic, checked here):
  (i)  Parseval:  sum_a |Corr(a)|^2 = (1/n) sum_d |F(x_d)|^2 <= ||F||_inf^2
       => leakage is SPARSE in frequency (<= 1/eps^2 freqs with |Corr|>=eps) -- but a perfect
       leak SATURATES this, so L^2 CANNOT close the question.
  (ii) exact identity:  sum_b |T(a,b)|^2 = p(n-1)  for a != 0   (uses x_d=x_d' <=> d'=+-d)
       => Cauchy-Schwarz gives |Corr| <= sqrt(pn)/n ~ 1 = VACUOUS.
  Both verified numerically below as a CHECK ON THE ALGEBRA (not as the proof).

DIRECTION 2 (the hunt):
  (a) EXACT symmetry: d->lam*d (GLV, lam^3=1 mod n) sends x_d -> beta*x_d, so
         T(a,b) = T(a*lam, b*beta)      -- a mu_3 symmetry IN THE FREQUENCY PLANE.
  (b) THE ALIGNED READOUT: set F^(b) := conj(T(a0,b))/|T(a0,b)|. Then
         Corr(a0) = (1/n) sum_b |T(a0,b)|   -- maximal, no cancellation.
      This readout EXISTS and leaks. So there is NO information-theoretic barrier; only
      COMPUTABILITY protects the curve (building F^ requires knowing T = knowing x_d).
      We demonstrate it explicitly vs a random-phase control.
  (c) Hunt: any computable phase pattern in arg T(a,b) BEYOND the mu_3 symmetry?

Float used for the analytic character sums (roots of unity, |T|~sqrt p) -- no key in path.
"""
import cmath, math, random
import numpy as np
from sympy import isprime
from hybrid_char_sum_v1 import legendre, tonelli, find_point, padd, mul, curve_points_order


def orbit_x(G, p, n):
    """xs[d] = x([d]G) for d=0..n-1;  xs[0]=None (identity)."""
    xs = [None] * n; acc = None
    for d in range(1, n):
        acc = padd(acc, G, p)
        xs[d] = acc[0]
    return xs


def build_T(xs, p, n):
    """T[a,b] = sum_d e_p(b x_d) e_n(a d)  -- via FFT over d for each b."""
    T = np.zeros((n, p), dtype=complex)
    idx = [d for d, x in enumerate(xs) if x is not None]
    xv = np.array([xs[d] for d in idx])
    for b in range(p):
        seq = np.zeros(n, dtype=complex)
        seq[idx] = np.exp(2j * np.pi * (b * xv % p) / p)
        T[:, b] = np.fft.fft(seq)          # sum_d seq[d] e^{-2pi i a d/n}; conj-convention ok
    return T


def cube_root_modp(p):
    e = (p - 1) // 3; g = 2
    while pow(g, e, p) == 1: g += 1
    return pow(g, e, p)


def main():
    # small curve with PRIME order
    p = None
    for q in range(200, 2000):
        if isprime(q) and q % 3 == 1:
            m = curve_points_order(q)
            if isprime(m):
                G = find_point(q)
                if mul(G, m, q) is None:
                    p, n, Gp = q, m, G; break
    print(f"curve y^2=x^3+7 / F_{p},  |<G>| = n = {n} (prime)")
    xs = orbit_x(Gp, p, n)
    T = build_T(xs, p, n)

    # ---- Direction 1 checks (algebra check, not proof) ----
    print("\n[D1] analytic identities (numerical CHECK of the derivation):")
    for a in (1, 2, 7):
        s = float(np.sum(np.abs(T[a, :]) ** 2))
        print(f"   a={a}: sum_b |T(a,b)|^2 = {s:.1f}   predicted p(n-2) = {p*(n-2)}   "
              f"ratio {s/(p*(n-2)):.6f}   [d'=-d pairs give -1, not 0 -- numerics caught this]")
    # Parseval check with a random bounded readout
    rng = np.random.default_rng(0)
    Fx = rng.choice([1, -1], size=p).astype(complex)          # |F|=1
    c = np.array([Fx[x] if x is not None else 0 for x in xs])
    Corr = np.fft.fft(c) / n
    print(f"   Parseval: sum_a |Corr|^2 = {float(np.sum(np.abs(Corr)**2)):.6f}  "
          f"predicted (1/n)sum|F(x_d)|^2 = {float(np.sum(np.abs(c)**2)/n):.6f}")
    print("   => L^2 bounds hold, and are SATURATED by a perfect leak => cannot close leakage.")

    # ---- Direction 2a: exact mu_3 symmetry in the frequency plane ----
    b1 = cube_root_modp(p); lam = beta = None
    lams = [c for c in range(2, n) if pow(c, 3, n) == 1]
    for bb in (b1, b1 * b1 % p):
        for cand in lams:
            if all(xs[(cand * d) % n] == (bb * xs[d]) % p for d in range(1, 40)):
                lam, beta = cand, bb; break
        if lam: break
    print(f"\n[D2a] GLV: lambda={lam} (lam^3=1 mod n), beta={beta};  x_([lam d]G) = beta*x_([d]G) ✓")
    err = max(abs(T[a % n, b] - T[(a * lam) % n, (b * beta) % p])
              for a in range(1, 12) for b in range(1, 12))
    print(f"   EXACT frequency-plane symmetry  T(a,b) = T(a*lam, b*beta):  max |diff| = {err:.2e}")

    # ---- Direction 2b: THE ALIGNED READOUT — the leak exists ----
    print("\n[D2b] the ALIGNED readout (does the leak exist at all?):")
    a0 = 1
    Fhat = np.zeros(p, dtype=complex)
    nz = np.abs(T[a0, :]) > 1e-9
    Fhat[nz] = np.conj(T[a0, nz]) / np.abs(T[a0, nz])       # unit modulus, phase-aligned
    Fhat[0] = 0                                              # drop the trivial mean term
    # F(x) = sum_b Fhat(b) e_p(b x)   (inverse DFT, unnormalised)
    F = np.fft.ifft(Fhat) * p
    cA = np.array([F[x] if x is not None else 0 for x in xs])
    CorrA = np.fft.fft(cA) / n
    leak_aligned = abs(CorrA[a0]) / np.max(np.abs(F))
    # control: random-phase readout of the same shape
    Fh2 = np.zeros(p, dtype=complex)
    Fh2[nz] = np.exp(2j * np.pi * rng.random(int(nz.sum())))
    Fh2[0] = 0
    F2 = np.fft.ifft(Fh2) * p
    c2 = np.array([F2[x] if x is not None else 0 for x in xs])
    Corr2 = np.fft.fft(c2) / n
    leak_rand = abs(Corr2[a0]) / np.max(np.abs(F2))
    print(f"   ALIGNED : |Corr(a0)|/||F||_inf = {leak_aligned:.4f}   "
          f"(predicted (1/n)sum_b|T| / ||F||_inf, NO cancellation)")
    print(f"   RANDOM  : |Corr(a0)|/||F||_inf = {leak_rand:.4f}   (generic readout)")
    print(f"   ratio aligned/random = {leak_aligned/max(leak_rand,1e-12):.1f}x")
    print("   => the LEAKING readout EXISTS and is far from noise. There is NO information-")
    print("      theoretic barrier; only COMPUTABILITY (building F^ needs T, i.e. needs x_d).")

    # ---- Direction 2c: any phase pattern beyond mu_3? ----
    print("\n[D2c] hunt: is arg T(a,b) predictable beyond the mu_3 symmetry?")
    ph = np.angle(T[1:, 1:])                                  # phases, a,b != 0
    # test 1: are phases uniform? (circular mean magnitude ~ 1/sqrt(N) if uniform)
    R = abs(np.mean(np.exp(1j * ph)))
    N = ph.size
    print(f"   circular-mean |R| = {R:.5f}  vs uniform-null ~1/sqrt(N) = {1/math.sqrt(N):.5f}")
    # test 2: is arg T(a,b) ~ linear in (a,b)? correlate with a*b, a+b mod small
    for name, g in [("a*b mod p", lambda A, B: (A * B) % p),
                    ("a+b", lambda A, B: A + B),
                    ("a*b^2", lambda A, B: (A * B * B) % p)]:
        A, B = np.meshgrid(np.arange(1, n), np.arange(1, p), indexing='ij')
        gv = g(A, B).astype(float)
        # circular-linear association: |mean exp(i(ph - 2pi g/p))|
        r = abs(np.mean(np.exp(1j * (ph - 2 * np.pi * gv / p))))
        print(f"   phase vs {name:10}: |mean e^(i(argT - 2pi g/p))| = {r:.5f} "
              f"(~{1/math.sqrt(N):.5f} = no pattern)")


if __name__ == "__main__":
    main()
