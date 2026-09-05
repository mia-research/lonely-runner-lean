#!/usr/bin/env python3
"""
Handover-2 §6 Int.1 — the frame/Gram operator on the Eisenstein lift, split by
mu3-core (eps=0) vs flaps (eps=+-), with lambda_max/Tr the observable.

DEFINITION USED (stated so it can be corrected): C = sum_x eis(x) eis(x)^T, the 2x2
second-moment of the lift vectors in the TRUE Eisenstein embedding (u,v) -> (u-v/2,
v*sqrt3/2). Observable lambda_max/Tr in [1/2,1]; =1/2 iff isotropic.

PREDICTION (the idea's content): the mu3-core is 120deg-rotation-invariant, and a
120deg-symmetric point set has an EXACTLY isotropic 2nd moment (C ∝ I). So the core
gives lambda_max/Tr = 1/2 exactly, and ALL anisotropy of the full frame operator
comes from the flaps -> "lambda_max/Tr governed by the flap fraction." Test:
  (1) is C_core exactly isotropic? (exact integer sums S_uu,S_uv,S_vv)
  (2) C_flap anisotropy; C_all anisotropy = only from flaps (C_all=C_core+C_flap,
      C_core ∝ I).
  (3) how does lambda_max/Tr(all)-1/2 relate to the flap fraction -- by COUNT (1/4)
      or by TRACE (flaps=high-norm shell, trace-weight > 1/4)?
Exact integer sums; float only in the final sqrt (analytic anisotropy).
"""
import math
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv, enorm
from glv_fundamental_domain_law_v1 import cube_roots


def build(p):
    R1, R2 = reduced_basis(p); DET = R1[0] * R2[1] - R1[1] * R2[0]
    R1t, R2t = tuple(R1), tuple(R2)
    b1, b2 = cube_roots(p)

    def eis(X):
        X %= p
        c1 = rdiv(X * R2[1], DET); c2 = rdiv(-X * R1[1], DET)
        return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))

    def om2(w): u, v = w; return (v - u, -u)
    def reduce_P(a, b):
        c1 = rdiv(a * R2[1] - b * R2[0], DET); c2 = rdiv(b * R1[0] - a * R1[1], DET)
        return (a - (c1 * R1[0] + c2 * R2[0]), b - (c1 * R1[1] + c2 * R2[1]))
    beta = b1 if eis((b1 * 12345) % p) == reduce_P(*om2(eis(12345))) else b2

    def eps(X):
        U0 = eis(X); U1 = eis((beta * X) % p)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0): return 0
        if c == R1t or c == R2t or c == (-R1t[0], -R1t[1]) or c == (-R2t[0], -R2t[1]): return 1
        return 2
    return eis, eps


def moments(pts):
    Suu = Suv = Svv = 0
    for (u, v) in pts:
        Suu += u * u; Suv += u * v; Svv += v * v
    return Suu, Suv, Svv


def aniso(Suu, Suv, Svv):
    # C_xx-C_yy = Suu - Suv - Svv/2 ; 4 C_xy^2 = 3(Suv - Svv/2)^2 ; Tr = Suu-Suv+Svv
    d = Suu - Suv - Svv / 2.0
    off = Suv - Svv / 2.0
    disc = d * d + 3 * off * off
    Tr = Suu - Suv + Svv
    lam_over_tr = 0.5 + math.sqrt(disc) / (2 * Tr) if Tr else 0.5
    # exact isotropy check: iso iff Suu==Svv and 2*Suv==Svv
    iso_exact = (Suu == Svv) and (2 * Suv == Svv)
    return lam_over_tr, Tr, iso_exact


def main():
    p = 100003
    eis, eps = build(p)
    core = []; flap = []
    for x in range(1, p):
        w = eis(x); e = eps(x)
        (core if e == 0 else flap).append(w)
    allpts = core + flap
    print(f"Int.1 frame operator, full lift F_p (p={p}); |core|={len(core)} |flap|={len(flap)}"
          f" flap-count-frac={len(flap)/(len(core)+len(flap)):.4f}\n")

    for name, pts in [("CORE (eps=0)", core), ("FLAP (eps=±)", flap), ("ALL", allpts)]:
        Suu, Suv, Svv = moments(pts)
        lot, Tr, iso = aniso(Suu, Suv, Svv)
        print(f"  {name:14s}: lambda_max/Tr = {lot:.6f}  (aniso {lot-0.5:+.6f})  "
              f"Tr={Tr}  exact-isotropic={iso}")

    # trace-weighted flap fraction
    Tc = moments(core); Tf = moments(flap)
    trc = Tc[0] - Tc[1] + Tc[2]; trf = Tf[0] - Tf[1] + Tf[2]
    print(f"\n  flap fraction by COUNT = {len(flap)/len(allpts):.4f}; by TRACE (norm) = "
          f"{trf/(trc+trf):.4f}  (flaps=high-norm shell => trace-weight > 1/4)")
    print("  => if CORE exact-isotropic=True, ALL anisotropy is from the flaps: the")
    print("     frame operator's lambda_max/Tr is entirely a flap phenomenon (Int.1 claim).")

    # THEORY: P is a 60deg rhombus, half-diagonals ratio sqrt3:1 (long:short); the
    # uniform 2nd moment gives lambda_max/Tr = 3/4 EXACTLY (=3/(3+1)), theta-independent.
    # Core (120deg-sym) = 1/2 exact. So 3/4 - 1/2 = 1/4 = flap fraction EXACTLY.
    print(f"\n  THEORY: uniform 60deg rhombus (diag ratio sqrt3:1) => lambda_max/Tr = 3/4")
    print(f"  exactly; core (120deg-sym) = 1/2 exactly; 3/4 - 1/2 = 1/4 = flap fraction.")
    print(f"  measured ALL = {aniso(*moments(allpts))[0]:.6f} (-> 3/4 as lattice fills P).")

    # secp check: theta-independent? (sampled)
    import random
    from glv_fundamental_domain_law_v1 import P_SECP, AP_SECP, BP_SECP
    from lift_sextant_rhombus_law_proof_v2 import gauss_reduce
    eiss, epss = build_secp()
    rng = random.Random(7)
    csec = []; fsec = []
    for _ in range(300000):
        x = rng.randrange(1, P_SECP); w = eiss(x)
        (csec if epss(x) == 0 else fsec).append(w)
    print("\n  secp (sampled 300k, different theta) — universality check:")
    for name, pts in [("CORE", csec), ("ALL", csec + fsec)]:
        lot, Tr, iso = aniso(*moments(pts))
        print(f"    {name:5s}: lambda_max/Tr = {lot:.5f}  exact-iso={iso}")


def build_secp():
    from glv_fundamental_domain_law_v1 import make_lift, cube_roots, P_SECP, AP_SECP, BP_SECP
    from lift_sextant_rhombus_law_proof_v2 import gauss_reduce
    R1, R2 = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    R1, R2, DET, reduce_P, eis = make_lift(P_SECP, R1, R2)
    R1t, R2t = tuple(R1), tuple(R2); b1, b2 = cube_roots(P_SECP)
    def om2(w): u, v = w; return (v - u, -u)
    beta = b1 if eis((b1 * 12345) % P_SECP) == reduce_P(*om2(eis(12345))) else b2
    def eps(X):
        U0 = eis(X); U1 = eis((beta * X) % P_SECP)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0): return 0
        if c in (R1t, R2t, (-R1t[0], -R1t[1]), (-R2t[0], -R2t[1])): return 1
        return 2
    return eis, eps


if __name__ == "__main__":
    main()
