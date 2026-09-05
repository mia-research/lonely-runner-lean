#!/usr/bin/env python3
"""
flap_sign_parity_v1.py — the two intertwining Z/2's, with Frobenius/slippage as REFERENCE.

User's idea: the two 1/8 flaps (+/-) and the x-even / y-odd gradings are two intertwining
parts; use the Frobenius/slippage fixed point NOT as an expansion point but as a REFERENCE
to understand how they interact.

Made precise:
  * flap sign  sigma(x) = sign(u+v) when |u+v|>1/2   (Cap Law: the two caps on the long
    diagonal; the +-1/8 pair). (u,v) = coefficients of eis(x) in the reduced basis.
  * parities:  x([-d]G)=x([d]G) EVEN in d ;  y([-d]G)=-y([d]G) ODD in d.
  * DIFFERENT involutions: sigma flips under FIELD negation x->-x (lift symmetry, since
    eis(-x)=-eis(x) => u+v -> -(u+v)); s_y flips under CURVE negation d->-d. Field negation
    is NOT a curve map. The Frobenius identity (1-pi)-1 = -pi is the Z[omega] relation tying
    the slippage operation to negation -- the reference where the two involutions meet.

Under v14's lens (THE LEAK = a phase-ALIGNED computable readout; misaligned provably sees
sqrt(p) noise), this CM-derived family is the PRINCIPLED candidate set the phase hunt needs
(vs the ad-hoc a*b guesses that found nothing).

TEST: for each candidate readout F, max_{a!=0}|Corr(a)|/||F||_inf, vs
  - random-readout baseline ~1/sqrt(n)  (misaligned)
  - the ALIGNED readout ~0.37 (v14)
Anomalously high => phase structure => the leak. Exact lift arithmetic (Fraction).
"""
import math
from fractions import Fraction as Fr
import numpy as np
from sympy import isprime
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import reduced_basis
from hybrid_char_sum_v1 import find_point, padd, mul, curve_points_order


def coeffs(z, R1, R2, DET):
    """exact coefficients (u,v) of z = u*R1 + v*R2 (Cramer)."""
    u = Fr(z[0] * R2[1] - z[1] * R2[0], DET)
    v = Fr(z[1] * R1[0] - z[0] * R1[1], DET)
    return u, v


def main():
    # small curve with PRIME order and p = 1 mod 3
    for q in range(200, 2000):
        if isprime(q) and q % 3 == 1:
            m = curve_points_order(q)
            if isprime(m):
                G = find_point(q)
                if mul(G, m, q) is None:
                    p, n, Gp = q, m, G; break
    print(f"y^2=x^3+7 / F_{p},  n=|<G>|={n} (prime)")
    eis, eps = build(p)
    R1, R2 = reduced_basis(p); R1 = tuple(R1); R2 = tuple(R2)
    DET = R1[0] * R2[1] - R1[1] * R2[0]

    # the cap is along the LONG diagonal; which of R1+R2 / R1-R2 that is flips with the
    # reduced-basis orientation (<R1,R2> = +-p/2), so DETECT it against eps.
    def _sig(x, plus):
        u, v = coeffs(eis(x), R1, R2, DET)
        s = (u + v) if plus else (u - v)
        if abs(s) <= Fr(1, 2): return 0
        return 1 if s > 0 else -1
    plus = sum(1 for x in range(1, p) if (_sig(x, True) != 0) == (eps(x) != 0))
    minus = sum(1 for x in range(1, p) if (_sig(x, False) != 0) == (eps(x) != 0))
    USE_PLUS = plus >= minus
    print(f"    [basis orientation] |u+v| matches eps {plus}/{p-1}; |u-v| matches {minus}/{p-1}"
          f"  => using |u{'+' if USE_PLUS else '-'}v|")

    def sigma_of_x(x):
        return _sig(x, USE_PLUS)

    # ---- 1. flap sign densities: 3/4 core : 1/8 (+) : 1/8 (-) ----
    cnt = {0: 0, 1: 0, -1: 0}
    for x in range(p):
        cnt[sigma_of_x(x)] += 1
    tot = p
    print(f"\n[1] flap-sign densities over F_{p}: core {cnt[0]/tot:.4f} (3/4=0.75), "
          f"+ {cnt[1]/tot:.4f}, - {cnt[-1]/tot:.4f}  (1/8=0.125 each)")
    agree = sum(1 for x in range(1, p) if (sigma_of_x(x) != 0) == (eps(x) != 0))
    print(f"    sigma!=0  <=>  eps!=0 : {agree}/{p-1} agree  (Cap Law consistency)")

    # ---- 2. the two involutions ----
    odd_field = all(sigma_of_x((-x) % p) == -sigma_of_x(x) for x in range(1, p))
    print(f"\n[2] involutions:")
    print(f"    sigma(-x) = -sigma(x)  (FIELD negation, a LIFT symmetry): {odd_field}")

    # orbit
    xs = [None] * n; ys = [None] * n; acc = None
    for d in range(1, n):
        acc = padd(acc, Gp, p); xs[d] = acc[0]; ys[d] = acc[1]
    even_x = all(xs[(-d) % n] == xs[d] for d in range(1, n))
    odd_y = all(ys[(-d) % n] == (-ys[d]) % p for d in range(1, n))
    print(f"    x([-d]G)=x([d]G) (EVEN in d): {even_x};  y([-d]G)=-y([d]G) (ODD in d): {odd_y}")
    # => sigma is EVEN in d (function of x); s_y is ODD in d. Different involutions.
    sig = np.array([sigma_of_x(xs[d]) if xs[d] is not None else 0 for d in range(n)])
    sy = np.array([1 if (ys[d] is not None and ys[d] % 2 == 0) else (-1 if ys[d] is not None else 0)
                   for d in range(n)])
    sig_even = all(sig[(-d) % n] == sig[d] for d in range(1, n))
    sy_odd = all(sy[(-d) % n] == -sy[d] for d in range(1, n))
    print(f"    => sigma EVEN in d: {sig_even};  s_y ODD in d: {sy_odd}  "
          f"=> product sigma*s_y is ODD in d")

    # ---- 3. THE PHASE-ALIGNMENT TEST (v14 lens) ----
    # baseline: max over n-1 frequencies of |Corr|~1/sqrt(n) is ~sqrt(2 ln n / n)
    base = math.sqrt(2 * math.log(n) / n)
    print(f"\n[3] phase alignment: max_(a!=0)|Corr(a)|/||F||_inf   "
          f"(MISALIGNED max-over-freq baseline ~sqrt(2 ln n/n)={base:.4f}; ALIGNED (v14) ~0.37)")

    def leak(F, label):
        F = np.asarray(F, dtype=complex)
        C = np.fft.fft(F) / n
        C[0] = 0                                  # drop the trivial mean (a=0)
        mx = float(np.max(np.abs(C)))
        nrm = float(np.max(np.abs(F))) or 1.0
        r = mx / nrm
        flag = "ALIGNED?" if r > 3 * base else "misaligned (noise floor)"
        print(f"    {label:28} max|Corr|/||F||_inf = {r:.4f}   {flag}")
        return r

    leak(sig, "sigma (flap sign)")
    leak(sy, "s_y (y-parity)")
    leak(sig * sy, "sigma * s_y  (ODD, the mix)")
    leak((sig != 0).astype(float), "1[flap]  (eps indicator)")
    rng = np.random.default_rng(1)
    leak(rng.choice([-1.0, 1.0], size=n), "[ctrl] random +-1")
    leak(np.exp(2j * np.pi * rng.random(n)), "[ctrl] random phase")

    print("\n  NOTE (grades): sigma and 1[flap] are functions of x with LOW Wiener norm")
    print("  (lattice-region indicators, Lemma W) => the CLOSURE THEOREM already covers them")
    print("  => provably negligible correlation. s_y is NOT a function of x, so it is OUTSIDE")
    print("  closure -- but it is the KNOWN free parity bit (d vs n-d, ~1 bit, already counted).")
    print("  The interesting object is the MIX sigma*s_y: half-covered, odd, CM-derived.")


if __name__ == "__main__":
    main()
