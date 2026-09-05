#!/usr/bin/env python3
"""
glv_pinned_satotate_v1.py

Grounds "which wedges are CM-stable" in the Frobenius arithmetic.

The pinned (CM-stable) sextant pair is a function of theta = arg(pi_p) mod 60 deg -- and
theta IS the Frobenius / Sato-Tate angle of the ideal (pi_p): for pi_p = (t + f*sqrt(-3))/2
(4p = t^2 + 3 f^2), arg(pi_p) = atan2(f*sqrt3, t). So the stable wedges are readable straight
off the trace t.

We (1) sweep primes, get pinned pair vs theta_geom (from the exact reduced basis), find the
exact switch; (2) confirm theta_geom == atan2(f*sqrt3, t) mod 60 (Frobenius angle); (3) do secp
from its actual trace t.

Pinned pair from exact Fraction sector areas; theta is a float label / arithmetic cross-check.
"""
import math
from fractions import Fraction as F
from lift_sextant_rhombus_law_proof_v2 import cornacchia_4p_D3, gauss_reduce, sector_props, theta_of

DEG = 180.0 / math.pi
P_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
T_SECP = 432420386565659656852420866390673177327   # Frobenius trace of E: y^2=x^3+7 over F_p


def pinned(R1, R2):
    pr = sector_props(R1, R2)
    return tuple(t for t in range(6) if pr[t] == F(1, 8))


def theta_from_t(p, t):
    """arg(pi_p) in degrees from the trace: pi_p = (t + f sqrt(-3))/2, 4p = t^2 + 3 f^2."""
    f2 = (4 * p - t * t)
    assert f2 % 3 == 0
    f = math.isqrt(f2 // 3)
    return math.degrees(math.atan2(f * math.sqrt(3), t))


def main():
    print("=" * 70)
    print("Pinned (CM-stable) wedges as a function of the Frobenius angle theta")
    print("=" * 70)
    import sympy
    rows = []
    for q in [x for x in sympy.primerange(1000, 500000) if x % 3 == 1][::300]:
        pi = cornacchia_4p_D3(q)
        if not pi:
            continue
        R1, R2 = gauss_reduce((pi[0], pi[1]), (-pi[1], pi[0] - pi[1]))
        th = theta_of(R1) * DEG
        rows.append((th, pinned(R1, R2), q, pi))
    rows.sort()
    # rule check: {1,4} below a threshold, {0,3} above
    def rule(th):
        return (1, 4) if th < 30 else (0, 3)
    viol = [(th, pin) for th, pin, _, _ in rows if pin != rule(th)]
    print(f"\n  swept {len(rows)} primes.  rule: pinned = {{1,4}} if theta<30 else {{0,3}}")
    print(f"  violations of that rule: {len(viol)}")
    # show the switch region
    print("  theta near the switch (deg -> pinned):")
    for th, pin, q, _ in rows:
        if 26 < th < 34:
            print(f"    theta={th:6.3f}  pinned={pin}   (p={q})")

    # (2) theta_geom == Frobenius angle from t (cross-check on a few)
    print("\n  theta_geom vs atan2(f*sqrt3, t) mod 60  (Frobenius-angle identity):")
    for th, pin, q, pi in rows[::max(1, len(rows) // 6)]:
        t = 2 * pi[0] - pi[1]                       # trace of this ideal generator
        thf = theta_from_t(q, t) % 60
        print(f"    p={q:>7}  theta_geom={th:7.3f}  atan2-form mod60={thf:7.3f}  "
              f"{'ok' if abs(th - thf) < 1e-6 or abs(th - thf - 60) < 1e-6 else 'DIFF'}")

    # (3) secp from its ACTUAL curve Frobenius pi_p = (AP,BP) = (t + f sqrt-3)/2
    AP, BP = 367917413016453100223835821029139468249, 303414439467246543595250775667605759171
    print("\n  --- secp256k1 (actual curve Frobenius pi_p = (AP,BP), trace t) ---")
    R1, R2 = gauss_reduce((AP, BP), (-BP, AP - BP))
    th = theta_of(R1) * DEG
    thf = theta_from_t(P_SECP, T_SECP) % 60
    print(f"    Frobenius angle from t : atan2(f*sqrt3,t) mod60 = {thf:.4f} deg")
    print(f"    theta_geom (pi_p basis)                        = {th:.4f} deg  "
          f"{'== t-form' if abs(th-thf)<1e-3 else 'DIFF'}")
    print(f"    pinned pair = {pinned(R1, R2)}   (theta=50.55 > 30 -> {{0,3}})")
    # the conjugate prime pi_bar above p (arg -> 60-theta) gives the MIRROR pinned pair
    piB = cornacchia_4p_D3(P_SECP)                          # cornacchia returns pi_bar here
    R1b, R2b = gauss_reduce((piB[0], piB[1]), (-piB[1], piB[0] - piB[1]))
    print(f"    conjugate pi_bar: theta={theta_of(R1b)*DEG:.4f} (=60-theta), "
          f"pinned={pinned(R1b, R2b)}  => the pinned pair encodes WHICH prime above p / sign of the Frobenius angle")


if __name__ == "__main__":
    main()
