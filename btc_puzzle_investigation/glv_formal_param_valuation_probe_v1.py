#!/usr/bin/env python3
"""
glv_formal_param_valuation_probe_v1.py

Test the idea (formal-group p-adic valuation of the scalar multiple):
  T_d = -x([d]G)/y([d]G),  v_p(T_d), vs lift-norm s_d and orbit label eps(d).

IDEA-LEVEL CHECK (the point of "test the idea not the method"): the formal group
linearizes E_1(Q_p) = kernel of reduction (points of the char-0 curve reducing to O
mod p). The puzzle points [d]G live in E(F_p) -- already reduced. For (x,y) in
E(F_p), T=-x/y is an element of F_p, which has NO nontrivial valuation: every
nonzero element is a unit, so v_p(T_d)=0 identically (only exception: x_d=0, a
single point). So the hypothesized v_p-shell structure cannot exist on the DLP
group. This script DEMONSTRATES that (not just asserts it):
  (1) count d in 1..N with x_d=0 or y_d=0 (the only source of nontrivial v_p);
  (2) show T_d is a unit for all others -> v_p identically 0, nothing to correlate;
  (3) the SALVAGEABLE intent -- does d's small-prime structure predict the norm
      SHELL s_d or eps(d)? -- is last turn's eps(d) vs d mod k (null @ N=300k,
      understood via GLV-orbit-invariance + closure); shown here small-N for context.
Exact integers throughout.
"""
from collections import Counter
from ecc_secp256k1 import scalar_mul, N_ORDER, P as p
from glv_fundamental_domain_law_v1 import make_lift, cube_roots, AP_SECP, BP_SECP
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce, enorm
from fractions import Fraction as F


def om2(w):
    u, v = w
    return (v - u, -u)


def add_affine(P1, P2):
    if P1 is None: return P2
    if P2 is None: return P1
    x1, y1 = P1; x2, y2 = P2
    if x1 == x2:
        if (y1 + y2) % p == 0: return None
        lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def main():
    R1, R2 = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    R1, R2, DET, reduce_P, eis = make_lift(p, R1, R2)
    b1, b2 = cube_roots(p)
    beta = b1 if eis((b1 * 12345) % p) == reduce_P(*om2(eis(12345))) else b2
    R1t, R2t = tuple(R1), tuple(R2)

    def eps_of_x(x):
        U0 = eis(x); U1 = eis((beta * x) % p)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0): return 1
        if c == R1t or c == R2t: return 2
        if c == (-R1t[0], -R1t[1]) or c == (-R2t[0], -R2t[1]): return 0
        return 3

    def normbucket(x):
        s = F(enorm(eis(x)), p)
        return 0 if s < F(3, 16) else (1 if s < F(1, 4) else 2)

    N = 3000
    G = scalar_mul(1)
    cur = G
    n_x0 = n_y0 = 0
    Tvals = set()
    recs = []
    for d in range(1, N + 1):
        x, y = cur
        if x == 0: n_x0 += 1
        if y == 0: n_y0 += 1
        # T_d = -x/y in F_p (a unit unless x=0)
        if y != 0:
            Td = (-x) * pow(y, -1, p) % p
            Tvals.add(Td == 0)  # track whether any T is 0
        recs.append((d, eps_of_x(x), normbucket(x)))
        cur = add_affine(cur, G)

    print("=" * 70)
    print("(1) v_p(T_d) structure on E(F_p) points  (T_d = -x/y in F_p)")
    print("=" * 70)
    print(f"  d = 1..{N}:  #{{x_d=0}} = {n_x0}   #{{y_d=0}} = {n_y0}")
    print(f"  T_d is a unit in F_p for all {N - n_x0} points with x_d != 0")
    print(f"  => v_p(T_d) = 0 IDENTICALLY (nonzero F_p elements have no valuation);")
    print(f"     the only nontrivial-valuation case is x_d=0 ({n_x0} of {N}).")
    print(f"  There is no v_p 'shell' gradation to correlate with s_d or eps(d):")
    print(f"  the formal group's p-adic valuation lives on E_1(Q_p) (kernel of")
    print(f"  reduction, points -> O mod p), a DIFFERENT group from E(F_p).")

    print("\n" + "=" * 70)
    print("(2) salvageable intent: d's small-prime structure vs SHELL s_d / eps(d)")
    print("=" * 70)
    # d mod 6 vs eps and vs norm-bucket (small N here; definitive is N=300k last turn)
    for lab, idx, k in [("eps", 1, 4), ("normbucket", 2, 3)]:
        J = [[0] * k for _ in range(6)]
        for d, e, nb in recs:
            J[d % 6][e if lab == "eps" else nb] += 1
        # crude: P(class | d%6) spread
        print(f"  {lab} vs d%6 (N={N}, context only): P({lab}=0..) by d%6 residue:")
        for r in range(6):
            tot = sum(J[r]) or 1
            print(f"    d%6={r}: " + " ".join(f"{J[r][c]/tot:.3f}" for c in range(k)))
    print("  (definitive: eps(d) vs d mod k NULL at N=300k, understood via GLV-orbit-")
    print("   invariance + closure -- glv_eps_chi2_tighten / _scalar_multiplicative).")


if __name__ == "__main__":
    main()
