#!/usr/bin/env python3
"""
glv_flap_pinned_sextant_v1.py

Closes the bridge between the 2-point CM law and the single-x pinned invariant.

The CM/GLV 2-point law (glv_fundamental_domain_law_v1) says the correction c(X) in
eis(beta X) = zeta.eis(X) + c fires (c != 0) on two 1/8-area "flaps" P \\ zeta^{-1}P.
The single-x angle law (lift_sextant_rhombus_law_v2) says exactly one opposite sextant
PAIR has area 1/8. Both are 1/8. Question: do the flap points coincide with the pinned
sextant pair -- exactly, as a subset, or not at all?

Here we cross-tabulate, over the WHOLE lattice (exact), the sextant of eis(X) against the
correction c in {-R1, 0, +R1} (zeta = omega, so R = R1). We identify the pinned pair
rigorously from the exact sector areas (== 1/8), and measure the set relationship.

Exact integers in the counting path; sector areas exact Fraction.
"""
import random
from fractions import Fraction as Fr
from lift_sextant_rhombus_law_proof_v2 import (
    reduced_basis, gauss_reduce, sector_props, sextant, rdiv, enorm, theta_of)

P_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
AP_SECP = 367917413016453100223835821029139468249
BP_SECP = 303414439467246543595250775667605759171


def om(w):
    u, v = w
    return (-v, u - v)


def om2(w):
    u, v = w
    return (v - u, -u)


def make_lift(p, R1=None, R2=None):
    if R1 is None:
        R1, R2 = reduced_basis(p)
    DET = R1[0] * R2[1] - R1[1] * R2[0]

    def reduce_P(a, b):
        c1 = rdiv(a * R2[1] - b * R2[0], DET)
        c2 = rdiv(b * R1[0] - a * R1[1], DET)
        return (a - (c1 * R1[0] + c2 * R2[0]), b - (c1 * R1[1] + c2 * R2[1]))

    def eis(X):
        return reduce_P(X % p, 0)

    return R1, R2, DET, reduce_P, eis


def _basis_coord(c, R1, R2, DET):
    a, b = c
    return ((a * R2[1] - b * R2[0]) // DET, (b * R1[0] - a * R1[1]) // DET)


def run(name, p, Xs, zeta, zname, R1=None, R2=None):
    R1, R2, DET, reduce_P, eis = make_lift(p, R1, R2)
    props = sector_props(R1, R2)
    pinned = tuple(s for s in range(6) if props[s] == Fr(1, 8))

    pure = [0] * 6
    flap = [0] * 6
    corr = {}                                   # correction vector -> count
    Xs = list(Xs)
    for X in Xs:
        w = eis(X)
        s = sextant(*w)
        wr = zeta(w)
        c = (reduce_P(*wr)[0] - wr[0], reduce_P(*wr)[1] - wr[1])
        if c == (0, 0):
            pure[s] += 1
        else:
            flap[s] += 1
            corr[c] = corr.get(c, 0) + 1

    marg = [pure[s] + flap[s] for s in range(6)]
    M = sum(marg)
    flap_free = tuple(s for s in range(6) if flap[s] == 0)
    flap_tot = sum(flap)
    flap_in_pinned = sum(flap[s] for s in pinned)

    th = theta_of(R1) * 180 / 3.141592653589793
    print(f"\n=== {name}  zeta={zname}  (theta={th:.2f} deg, M={M}) ===")
    print(f"    pinned pair (area==1/8): {pinned}     flap-FREE sextants: {flap_free}"
          f"     {'== MATCH' if set(flap_free) == set(pinned) else '!= differ'}")
    print(f"    sextant : marginal   flap(c!=0)  flap-rate")
    for s in range(6):
        tag = "  <-- pinned" if s in pinned else ""
        rate = flap[s] / marg[s] if marg[s] else 0
        print(f"      {s}    : {marg[s]:8d}  {flap[s]:8d}   {rate:.4f}{tag}")
    cvecs = {(_basis_coord(c, R1, R2, DET)): n for c, n in corr.items()}
    print(f"    corrections (m1*R1+m2*R2 : count): {cvecs}")
    print(f"    flap total = {flap_tot} ({flap_tot/M:.4f});  "
          f"P(sextant in pinned | flap) = {flap_in_pinned}/{flap_tot} = {flap_in_pinned/max(flap_tot,1):.4f}")


def main():
    print("=" * 74)
    print("Flap (CM correction) vs pinned sextant pair -- exact lattice cross-tab")
    print("=" * 74)
    import sympy
    small = [q for q in sympy.primerange(1000, 300000) if q % 3 == 1]
    # spread of theta => both pinned-pair classes {0,3} and {1,4} should appear
    picks = [small[0], small[len(small) // 5], small[2 * len(small) // 5],
             small[3 * len(small) // 5], small[4 * len(small) // 5], small[-1]]
    for p in picks:
        run(f"full F_p p={p}", p, range(1, p), om, "omega")

    rng = random.Random(31415)
    Xs = [rng.randrange(1, P_SECP) for _ in range(120000)]
    R1s, R2s = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    run("secp uniform-X", P_SECP, Xs, om, "omega", R1=R1s, R2=R2s)
    # both cube roots on one prime -> is flap-free == pinned for BOTH zeta?
    print("\n----- both cube roots on p=1009 -----")
    run("full F_p p=1009", 1009, range(1, 1009), om, "omega")
    run("full F_p p=1009", 1009, range(1, 1009), om2, "omega^2")


if __name__ == "__main__":
    main()
