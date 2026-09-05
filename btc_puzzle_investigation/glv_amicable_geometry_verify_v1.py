#!/usr/bin/env python3
"""
glv_amicable_geometry_verify_v1.py

VERIFICATION of the amicable-geometry claims (a colleague ran these by hand and self-flagged
a fabricated output; here we run them exactly against the real on-disk machinery).

Claims to check, exactly (Fraction / integer):
  1. Basis slippage R1_p - R1_n, R2_p - R2_n  (claimed single-digit integers).
  2. Overlap area(P_p ∩ P_n)/area(P_p)         (claimed 0.9999939561).
  3. mu3-core containment: is C_n ⊆ C_p?        (claimed prop(C_n shared)=1.0 exactly).
  4. Endomorphism orbit corrections c_i = U_{i+1} - omega^2 U_i:
       - c_i in {0, +-R}?   - orbit closes U_3=U_0?
       - which constraint holds:  c0 + w^2 c1 + c2 = 0  (colleague)  vs
                                  w c0 + w^2 c1 + c2 = 0  (algebra) ?
"""
import random
from fractions import Fraction as F
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce, enorm
from glv_fundamental_domain_geom_check_v1 import corners, om, om2, clip as sh_clip, shoelace, _ccw
from glv_fundamental_domain_law_v1 import make_lift, cube_roots

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
AP, BP = 367917413016453100223835821029139468249, 303414439467246543595250775667605759171


def poly_om(P4, f):
    return _ccw([f(c) for c in P4])


def mu3_core(R1, R2):
    P4 = corners(R1, R2)
    return _ccw(sh_clip(sh_clip(P4, poly_om(P4, om)), poly_om(P4, om2)))


def area_inter(A, B):
    c = sh_clip(_ccw(A), _ccw(B))
    return shoelace(_ccw(c)) if len(c) >= 3 else F(0)


def main():
    R1p, R2p = gauss_reduce((AP, BP), (-BP, AP - BP))
    R1n, R2n = gauss_reduce((AP - 1, BP), (-BP, (AP - 1) - BP))
    print("=" * 70)
    print("1. BASIS SLIPPAGE (pi_p vs pi_n = pi_p - 1)")
    print("=" * 70)
    print(f"   R1_p = {R1p}\n   R1_n = {R1n}\n   R1_p - R1_n = {(R1p[0]-R1n[0], R1p[1]-R1n[1])}")
    print(f"   R2_p = {R2p}\n   R2_n = {R2n}\n   R2_p - R2_n = {(R2p[0]-R2n[0], R2p[1]-R2n[1])}")

    print("\n" + "=" * 70)
    print("2. OVERLAP  area(P_p ∩ P_n)")
    print("=" * 70)
    Pp, Pn = corners(R1p, R2p), corners(R1n, R2n)
    aPp, aPn = shoelace(Pp), shoelace(Pn)
    inter = area_inter(Pn, Pp)
    print(f"   area(P_p) = {aPp}  (= p? {aPp == P})")
    print(f"   area(P_n) = {aPn}  (= n? {aPn == N})")
    print(f"   area(P_p ∩ P_n) = {inter}")
    print(f"   proportion of P_p = {float(F(inter, aPp)):.12f}   (1 - {float(1-F(inter,aPp)):.3e})")
    print(f"   proportion of P_n = {float(F(inter, aPn)):.12f}")
    print(f"   colleague claimed 0.9999939561 -> {'MATCH' if abs(float(F(inter,aPp))-0.9999939561)<1e-9 else 'REFUTED'}")

    print("\n" + "=" * 70)
    print("3. mu3-CORE CONTAINMENT  (is C_n ⊆ C_p ?)")
    print("=" * 70)
    Cp, Cn = mu3_core(R1p, R2p), mu3_core(R1n, R2n)
    aCp, aCn = shoelace(Cp), shoelace(Cn)
    cInter = area_inter(Cn, Cp)
    print(f"   area(C_p) = {aCp}  (= 3/4 p? {aCp == F(3,4)*P})")
    print(f"   area(C_n) = {aCn}  (= 3/4 n? {aCn == F(3,4)*N})")
    print(f"   area(C_n ∩ C_p) = {cInter}")
    print(f"   prop of C_n inside C_p = {float(F(cInter, aCn)):.12f}  "
          f"(C_n ⊆ C_p exactly? {cInter == aCn})")
    print(f"   prop of C_p shared     = {float(F(cInter, aCp)):.12f}")

    print("\n" + "=" * 70)
    print("4. ENDOMORPHISM ORBIT corrections + constraint")
    print("=" * 70)
    _, _, _, reduce_P, eis = make_lift(P, R1p, R2p)
    basis_set = {(0, 0): "0", tuple(R1p): "+R1", (-R1p[0], -R1p[1]): "-R1",
                 tuple(R2p): "+R2", (-R2p[0], -R2p[1]): "-R2"}
    b1, b2 = cube_roots(P)
    # select the cube root beta that gives small (in {0,+-R}) corrections vs omega^2
    def c_of(X, b):
        U0 = eis(X); U1 = eis((b * X) % P)
        return (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
    beta = b1 if c_of(12345, b1) in basis_set else b2
    print(f"   using beta = {'omega^2-matching root' if beta in (b1,b2) else '?'} "
          f"(so eis(beta X) = omega^2 eis(X) + c)")

    rng = random.Random(7)
    closed = allsmall = con_coll = con_alg = 0
    seen = {}
    T = 4000
    for _ in range(T):
        X0 = rng.randrange(1, P)
        U = [eis(X0)]
        Xi = X0
        for _i in range(3):
            Xi = (beta * Xi) % P
            U.append(eis(Xi))
        c = [(U[i+1][0]-om2(U[i])[0], U[i+1][1]-om2(U[i])[1]) for i in range(3)]
        closed += (U[3] == U[0])
        allsmall += all(tuple(ci) in basis_set for ci in c)
        for ci in c:
            seen[basis_set.get(tuple(ci), "OTHER")] = seen.get(basis_set.get(tuple(ci), "OTHER"), 0) + 1
        # colleague:  c0 + w^2 c1 + c2
        t1 = (c[0][0] + om2(c[1])[0] + c[2][0], c[0][1] + om2(c[1])[1] + c[2][1])
        # algebra:   w c0 + w^2 c1 + c2
        t2 = (om(c[0])[0] + om2(c[1])[0] + c[2][0], om(c[0])[1] + om2(c[1])[1] + c[2][1])
        con_coll += (t1 == (0, 0))
        con_alg += (t2 == (0, 0))
    print(f"   over {T} random orbits:")
    print(f"     orbit closes U3==U0:            {closed}/{T}")
    print(f"     all c_i in {{0,+-R1,+-R2}}:        {allsmall}/{T}   census={seen}")
    print(f"     colleague  c0 + w^2 c1 + c2 = 0: {con_coll}/{T}")
    print(f"     algebra   w c0 + w^2 c1 + c2 = 0: {con_alg}/{T}")
    verdict = ("ALGEBRA form holds" if con_alg == T and con_coll < T else
               "COLLEAGUE form holds" if con_coll == T and con_alg < T else
               "both hold (corrections often 0)" if con_coll == T and con_alg == T else "neither")
    print(f"   => {verdict}")


if __name__ == "__main__":
    main()
