#!/usr/bin/env python3
"""
glv_doubling_scaling_v1.py

Reassessment (honoring the caution: a single-N "null floor" is not a verdict).

For the doubling map phi2 (scalar x2), characterize MI(sextant X ; sextant 2X) at the
POPULATION level (exact full-F_p, no sampling) across growing p, and separately the
mu3-refined readout (sextant PARITY, the beta-invariant the [omega]-covariance forces).

Discriminator (signal_vs_noise_scaling): a genuine dependence gives MI that PLATEAUS
(MI*N grows ~ N); pure finite-size noise gives MI ~ 1/N (MI*N ~ const). We report MI*(p-1)
so the two are unambiguous -- no matched-null needed, this is the exact population value.
Exact integer counting; MI uses log2 as a reported statistic only.
"""
import math
from glv_fundamental_domain_law_v1 import make_lift, sextant, cube_roots, P_SECP, AP_SECP, BP_SECP
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce


def phi2(x, p):
    den = (4 * (pow(x, 3, p) + 7)) % p
    return None if den == 0 else ((pow(x, 4, p) - 56 * x) * pow(den, p - 2, p)) % p


def mi_bits(J):
    tot = sum(sum(r) for r in J)
    if not tot:
        return 0.0
    rs = [sum(r) for r in J]
    cs = [sum(J[i][j] for i in range(len(J))) for j in range(len(J[0]))]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
               for i in range(len(J)) for j in range(len(J[0]))
               if J[i][j] and rs[i] and cs[j])


def full_mi(p):
    _, _, _, _, eis = make_lift(p)
    J6 = [[0] * 6 for _ in range(6)]
    J2 = [[0] * 2 for _ in range(2)]
    for x in range(1, p):
        y = phi2(x, p)
        if y in (None, 0):
            continue
        a = sextant(*eis(x)); b = sextant(*eis(y))
        J6[a][b] += 1
        J2[a % 2][b % 2] += 1
    return mi_bits(J6), mi_bits(J2), sum(sum(r) for r in J6)


def main():
    print("=" * 68)
    print("Doubling on the lift: exact population MI(sextant X ; sextant 2X) vs scale")
    print("=" * 68)
    print(f"  {'p':>8} {'N':>8} {'MI6 (bits)':>12} {'MI6 * N':>10}   {'MI-parity':>10} {'*N':>8}")
    import sympy
    for p in [q for q in sympy.primerange(1000, 400000) if q % 3 == 1][::40][:8]:
        mi6, mi2, N = full_mi(p)
        print(f"  {p:>8} {N:>8} {mi6:>12.6f} {mi6*N:>10.1f}   {mi2:>10.6f} {mi2*N:>8.1f}")
    print("\n  Reading: if MI*N stays ~constant => MI ~ 1/N => sextant X _|_ sextant 2X")
    print("  asymptotically (the coarse sextant readout does not propagate through the")
    print("  scalar-doubling / group-law map). If MI*N GROWS ~ N => real dependence.")
    print("  (Parallels the proven sextant _|_ chi6: additive-geometric vs the group law.)")
    print("\n  NOTE: this is the COARSE 6-way (and 2-way parity) readout only. It does not")
    print("  speak to the full 2-D lift or joint-SET structure -- those remain open and are")
    print("  the right place to look (the pi_p<->pi_n amicable bridge, the S3 3-point law).")


if __name__ == "__main__":
    main()
