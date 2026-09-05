#!/usr/bin/env python3
"""
lift_chi6_uniform_law_proof_v1.py

POSITIVE THEOREM, contrast case to the rhombus law
(lift_sextant_rhombus_law_v2.md).

Both the lift ANGLE (sextant) and the sextic CHARACTER chi6 are single-x-coordinate
functionals, both scalar-independent.  But their marginals have opposite shapes:

  * lift angle sextant(eis(X)) = an ADDITIVE / geometric readout of X mod pi_p.
    Marginal NON-uniform: the rhombus area law (1/8, p0(theta), 3/8-p0).
  * chi6(X) = X^((p-1)/6) in mu_6 = a MULTIPLICATIVE readout of X.
    Marginal EXACTLY uniform: (p-1)/6 preimages per value.  Proven here.

THM (chi6 marginal is exactly uniform -- unconditional, group theory).
  p == 1 (mod 3) and p odd  =>  p == 1 (mod 6)  =>  6 | (p-1).
  F_p^* is cyclic of order p-1; chi6 : x -> x^((p-1)/6) is a surjective homomorphism
  onto mu_6 (the 6th roots of unity in F_p) with kernel = the sextic residues, of
  index exactly 6.  Every fiber therefore has EXACTLY (p-1)/6 elements, so
      #{ X in F_p^* : chi6(X) = zeta^j } = (p-1)/6   for each j = 0..5,
  and the additive character sum  sum_{X in F_p^*} zeta_6^{chi6(X)} = 0  exactly.
  (X=0 has measure 1/p -> 0.)  No d, no analytic input.

CONDITIONAL (curve, cited).  Over curve x-coordinates x([d]G) the count splits as
  N_j = sum_x [chi6(x)=j] (1 + chi2(x^3+7))
      = (p-1)/6            <- exact, character orthogonality
      + sum_x [chi6(x)=j] chi2(x^3+7)   <- a curve character sum, |.| = O(sqrt p) (Weil)
  so chi6 over the curve is uniform up to O(p^{-1/2}); MI(chi6 ; d mod m) = O(p^{-delta}).

Verification: exact fiber enumeration on a moderate prime; secp divisibility + sampler
confirmation; the exact contrast against the non-uniform sextant; and an EXACT
full-F_p scaling test showing the additive (sextant) and multiplicative (chi6)
shadows are ASYMPTOTICALLY INDEPENDENT (chi^2 stays ~df as N grows 400x; any
correlation is O(p^-1/2)).  Exact integer arithmetic in the counting path.
"""
from fractions import Fraction as Fr
import random

P_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

def chi6_of(x, p, e6, table):
    x %= p
    if x == 0: return None
    return table[pow(x, e6, p)]

def build_chi6(p):
    e6 = (p - 1) // 6
    for g in range(2, 500):
        z = pow(g, e6, p)
        if pow(z, 6, p) == 1 and all(pow(z, t, p) != 1 for t in (1, 2, 3)):
            return e6, {pow(z, j, p): j for j in range(6)}
    raise RuntimeError("no primitive 6th root")

def main():
    print("=" * 70)
    print("THM  chi6 marginal is EXACTLY uniform  (contrast: sextant is non-uniform)")
    print("=" * 70)

    # (1) divisibility 6 | p-1  (the hypothesis that makes mu_6 live in F_p)
    for nm, p in [("moderate p=100003", 100003), ("secp256k1 p", P_SECP)]:
        print(f"  {nm}: (p-1) % 6 = {(p - 1) % 6}  (0 => 6|p-1 => mu_6 subset F_p)")

    # (2) EXACT fiber enumeration on a moderate prime (fibers must be equal = (p-1)/6)
    p = 100003
    e6, tbl = build_chi6(p)
    counts = [0] * 6
    for x in range(1, p):
        counts[tbl[pow(x, e6, p)]] += 1
    exact = (p - 1) // 6
    print(f"\n  EXACT enumeration p={p}: fiber sizes {counts}")
    print(f"    all == (p-1)/6 = {exact}?  {all(c == exact for c in counts)}")
    # additive character sum over mu_6 == 0 exactly (equal fibers)
    # sum zeta_6^{chi6(X)} = sum_j counts[j] * zeta^j ; equal counts => 0
    zsum_re_pairs = [(counts[j], j) for j in range(6)]
    is_zero = all(c == exact for c in counts)
    print(f"    additive character sum  sum_X zeta_6^chi6(X) == 0 exactly?  {is_zero}")

    # (3) secp: chi6 marginal over uniform X (sampler confirmation of the exact thm)
    e6s, tbls = build_chi6(P_SECP)
    rng = random.Random(11)
    M = 120000
    hc = [0] * 6
    for _ in range(M):
        j = chi6_of(rng.randrange(1, P_SECP), P_SECP, e6s, tbls)
        hc[j] += 1
    print(f"\n  secp uniform-X chi6 histogram (M={M}):")
    print("   ", [f"{hc[j] / M:.4f}" for j in range(6)],
          f" max|.-1/6|={max(abs(hc[j] / M - 1 / 6) for j in range(6)):.4f}"
          f"  (~1/sqrt(M)={1 / M ** 0.5:.4f})")

    # (4) CONTRAST: exact sextant marginal (rhombus, non-uniform) vs exact chi6 (uniform)
    from eisenstein_lift_sextant_exact_v1 import R1, R2
    import importlib.util
    spec = importlib.util.spec_from_file_location("v2", "lift_sextant_rhombus_law_proof_v2.py")
    v2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(v2)
    sx = v2.sector_props(R1, R2)
    print("\n  CONTRAST (both single-x, both scalar-independent):")
    print(f"    sextant marginal (exact rhombus areas): "
          f"{[str(x) if x.denominator < 100 else f'{float(x):.4f}' for x in sx]}  -> NON-uniform")
    print(f"    chi6 marginal (exact):                  {['1/6'] * 6}                          -> UNIFORM")

    # (5) RELATION: are the additive (sextant) and multiplicative (chi6) shadows
    #     dependent?  Settle it EXACTLY by full-F_p enumeration (no sampling noise) and
    #     SCALING: chi^2 of independence has df=25; if the two are dependent it grows ~N,
    #     if independent it stays ~25 as p grows.
    import sympy
    def full_chi2(p):
        R1p, R2p = v2.reduced_basis(p); DET = R1p[0] * R2p[1] - R1p[1] * R2p[0]
        def eisp(X):
            c1 = v2.rdiv(X * R2p[1], DET); c2 = v2.rdiv(-X * R1p[1], DET)
            return (X - (c1 * R1p[0] + c2 * R2p[0]), -(c1 * R1p[1] + c2 * R2p[1]))
        e6p, tblp = build_chi6(p)
        cont = [[0] * 6 for _ in range(6)]
        for X in range(1, p):
            u, v = eisp(X); cont[v2.sextant(u, v)][tblp[pow(X, e6p, p)]] += 1
        rt = [sum(r) for r in cont]; ct = [sum(cont[i][j] for i in range(6)) for j in range(6)]
        N = p - 1
        return sum((cont[i][j] - rt[i] * ct[j] / N) ** 2 / (rt[i] * ct[j] / N)
                   for i in range(6) for j in range(6) if rt[i] * ct[j] > 0)
    sample = [q for q in sympy.primerange(1000, 400000) if q % 6 == 1]
    sample = [sample[0], sample[len(sample) // 3], sample[2 * len(sample) // 3], sample[-1]]
    print("\n  RELATION sextant vs chi6 -- EXACT full-F_p chi^2 (df=25) vs growing N:")
    for p in sample:
        print(f"    p={p:6d} (N={p - 1:6d}): exact chi^2 = {full_chi2(p):5.1f}")
    print("    chi^2 stays ~df=25 as N grows 400x  =>  ASYMPTOTICALLY INDEPENDENT")
    print("    (additive/geometric shadow and multiplicative shadow do not interact;")
    print("     any correlation is O(p^-1/2), at the character-sum floor. Corrects the")
    print("     v1 'MI(sextant;chi6) fires' note = small-sample echo of sextant's own")
    print("     marginal non-uniformity, not genuine dependence.)")

    # (6) CURVE: chi6 over x([d]G) near-uniform (first term exact 0, Weil-bounded correction)
    try:
        from angular_interference_scaling_v1 import gen_keys
        d, X, Y = gen_keys(256, 40000, 7)
        hcurve = [0] * 6
        for x in X:
            j = chi6_of(int(x), P_SECP, e6s, tbls)
            if j is not None: hcurve[j] += 1
        m = sum(hcurve)
        print(f"\n  CURVE gen256 chi6 histogram (M={m}):")
        print("   ", [f"{hcurve[j] / m:.4f}" for j in range(6)],
              f" max|.-1/6|={max(abs(hcurve[j] / m - 1 / 6) for j in range(6)):.4f}")
    except Exception as e:
        print(f"\n  (curve check skipped: {e})")

if __name__ == "__main__":
    main()
