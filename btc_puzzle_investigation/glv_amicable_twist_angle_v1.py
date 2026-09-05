#!/usr/bin/env python3
"""
glv_amicable_twist_angle_v1.py

Direction (2): the pinned / CM-stable locus is arg(pi_p)-locked. Does the SAME mu6-geometry
tie E/F_p to its amicable partner and its sextic twists?

Three Frobenius elements share the ring Z[omega]:
  * pi_p            -- Frobenius of E/F_p,  N = p,      arg mod 60 = theta_p  -> pinned_p
  * pi_n = pi_p - 1 -- prime above n (amicable), N = n,  arg mod 60 = theta_n  -> pinned_n
                       (the amicable curve E/F_n has Frobenius 1 - pi_p = -pi_n)
  * u * pi_p, u in mu6 -- the six sextic twists (same IDEAL (pi_p), so same rhombus).

Key point (amicable shift): pi_n and pi_p differ by the REAL unit 1, so
  |arg(pi_n) - arg(pi_p)| <= 1/|pi_p| = O(p^{-1/2}).
=> at cryptographic scale the amicable partner shares the pinned pair EXACTLY; the two
CM-stable loci coincide. We confirm this: pinned_p == pinned_n with a match-rate that -> 1
as p grows, and holds for secp (theta agree to ~38 digits).

Exact: pinned pairs from sector_props (exact Fraction areas). theta printed as a float label.
"""
from fractions import Fraction as F
from lift_sextant_rhombus_law_proof_v2 import (
    cornacchia_4p_D3, gauss_reduce, sector_props, enorm, theta_of)

P_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
AP, BP = 367917413016453100223835821029139468249, 303414439467246543595250775667605759171

DEG = 180.0 / 3.141592653589793


def rhombus_and_pinned(pi):
    """(reduced basis, pinned sextant pair) of the ideal (pi), pi=(a,b) in Z[omega]."""
    a, b = pi
    R1, R2 = gauss_reduce((a, b), (-b, a - b))
    props = sector_props(R1, R2)
    return R1, R2, tuple(t for t in range(6) if props[t] == F(1, 8))


def mul_omega(pi):
    a, b = pi
    return (-b, a - b)


def analyze(name, pi_p, verbose=True):
    R1p, R2p, pin_p = rhombus_and_pinned(pi_p)
    pi_n = (pi_p[0] - 1, pi_p[1])
    R1n, R2n, pin_n = rhombus_and_pinned(pi_n)
    tp = theta_of(R1p) * DEG
    tn = theta_of(R1n) * DEG
    if verbose:
        print(f"\n=== {name} ===")
        print(f"    pi_p         N={enorm(pi_p)}  theta_p={tp:6.2f}  pinned_p={pin_p}")
        print(f"    pi_n=pi_p-1  N={enorm(pi_n)}  theta_n={tn:6.2f}  pinned_n={pin_n}")
        print(f"    amicable pinned match: {pin_p == pin_n}   |theta_p-theta_n|={abs(tp-tn):.4g} deg "
              f"(bound 1/|pi_p| = {DEG/enorm(pi_p)**0.5:.3g} deg)")
        # six sextic twists = u*pi_p, u in mu6: all generate the ideal (pi_p), same rhombus
        print(f"    six sextic twists u*pi_p (u in mu6): share the ideal (pi_p) => identical "
              f"rhombus & pinned pair {pin_p}")
    return pin_p == pin_n


def main():
    print("=" * 72)
    print("Amicable & twist angle tie: does the pinned locus follow pi_p -> pi_n = pi_p-1 ?")
    print("=" * 72)

    # secp (exact, cryptographic scale)
    assert enorm((AP, BP)) == P_SECP and enorm((AP - 1, BP)) == N_SECP
    analyze("secp256k1  (N(pi_p)=p, N(pi_p-1)=n verified)", (AP, BP))

    # sweep: match-rate of pinned_p == pinned_n, binned by size of p, to show -> 1
    import sympy
    print("\n--- pinned_p == pinned_n  match-rate vs scale (amicable shift is O(p^-1/2)) ---")
    bins = [(10**3, 10**4), (10**4, 10**5), (10**5, 10**6), (10**6, 10**7)]
    for lo, hi in bins:
        ps = [q for q in sympy.primerange(lo, hi) if q % 3 == 1]
        step = max(1, len(ps) // 250)
        ps = ps[::step]
        m = 0; tot = 0
        for q in ps:
            pi = cornacchia_4p_D3(q)
            if pi is None:
                continue
            tot += 1
            m += analyze("", pi, verbose=False)
        print(f"    p in [{lo:>8},{hi:<8}): pinned match {m}/{tot} = {m/tot:.3f}")


if __name__ == "__main__":
    main()
