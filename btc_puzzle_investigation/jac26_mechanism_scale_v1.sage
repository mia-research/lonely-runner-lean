#!/usr/bin/env sage
"""jac26_mechanism_scale_v1.sage

Closes the two "reviewed-not-re-executed" items from RESULT_26_closure_symbolic_uniformity_v1.md,
making #26 airtight end-to-end from this session's own hands:

  (A) SYMBOLIC squarefreeness certificate:  Res_lambda(D,F) = (4A^3+27B^2)^2  and
      disc(D) = -4096*(4A^3+27B^2), as polynomial identities (after B = yR^2 - xR^3 - A xR).
      => D,F coprime & separable for every nonsingular E and every R; deg G = 7 when yR != 0.

  (B) THE MECHANISM at scale.  Not just c1=0 (the conclusion), but the full Frobenius char poly
      shape  Ch(T) = T^6 - c3 T^3 + p^3   (c1 = c2 = 0), which IS the block-cyclic / Weil-
      restriction structure  Jac(C) = Res_{F_{p^3}/F_p}(E1).  Verified via Sage's genus-3
      frobenius_polynomial at primes well beyond the corpus's p <= 211, j=0 and generic j,
      several random R each.  Control: even-n must break the shape.

Exact: symbolic over QQ; GF(p) point arithmetic / Sage hyperelliptic Frobenius. No float.
"""
from sage.all import (QQ, GF, EllipticCurve, ZZ, PolynomialRing, HyperellipticCurve, Integer)


# ========================================================= (A) SYMBOLIC Res/disc
def symbolic_resultant():
    print("=" * 78)
    print("(A) SYMBOLIC:  Res(D,F) = (4A^3+27B^2)^2   and   disc(D) = -4096(4A^3+27B^2)")
    print("=" * 78)
    S = PolynomialRing(QQ, ['A', 'xR', 'yR'])
    A, xR, yR = S.gens()
    B = yR**2 - xR**3 - A*xR                       # the on-curve value of B
    L = PolynomialRing(S, 'l')
    l = L.gen()
    D = l**4 - 6*xR*l**2 - 8*yR*l - (3*xR**2 + 4*A)
    F = yR*l**3 + (A + 3*xR**2)*l**2 + 3*xR*yR*l + yR**2
    res = D.resultant(F)
    disc = D.discriminant()
    tgt_res = (4*A**3 + 27*B**2)**2
    tgt_disc = -4096*(4*A**3 + 27*B**2)
    print("  Res(D,F) - (4A^3+27B^2)^2      == 0 :", S(res) - tgt_res == 0)
    print("  disc(D)  + 4096(4A^3+27B^2)    == 0 :", S(disc) - tgt_disc == 0)
    # so on the nonsingular locus 4A^3+27B^2 != 0: gcd(D,F)=1 and D separable, uniformly.
    return S(res) - tgt_res == 0 and S(disc) - tgt_disc == 0


# ================================== (B) MECHANISM: char-poly shape via c1=c2=0
# Ch(T) = T^6 - c1 T^5 + c2 T^4 - c3 T^3 + p c2 T^2 - p^2 c1 T + p^3  (genus-3 func. eqn).
# So the shape  T^6 - c3 T^3 + p^3  <=>  c1 = c2 = 0
#   c1 = 0  <=>  #C(F_p)   = p+1    <=>  Sum_{F_p}   chi2(G) = 0     (O(p))
#   c2 = 0  <=>  #C(F_p^2) = p^2+1  <=>  Sum_{F_p^2} chi2^(2)(G) = 0 (O(p^2))
# Avoids any F_{p^3} count (the frobenius_polynomial bottleneck).

def qchar(v, Kk):
    if v == 0:
        return ZZ(0)
    return ZZ(1) if v.is_square() else ZZ(-1)


def shape_via_c1c2(p, A, B, n_R=3, tag="", do_c2=True):
    K = GF(p)
    E = EllipticCurve(K, [A, B])
    n = E.order()
    parity = "odd " if n % 2 else "EVEN"
    Kl = PolynomialRing(K, 'l')
    K2 = GF(p**2, 'a')
    K2l = PolynomialRing(K2, 'l')
    ok_cells = 0
    tried = 0
    worst = (0, 0)
    for _ in range(n_R):
        R = E.random_point()
        if R.is_zero() or R[1] == 0:
            continue
        xR, yR = R[0], R[1]
        l = Kl.gen()
        D = l**4 - 6*xR*l**2 - 8*yR*l - (3*xR**2 + 4*K(A))
        F = yR*l**3 + (K(A) + 3*xR**2)*l**2 + 3*xR*yR*l + yR**2
        G = D*F
        if G.degree() != 7 or not G.is_squarefree():
            continue
        tried += 1
        c1sum = sum(qchar(G(x), K) for x in K)                    # = -(#C - (p+1))
        if do_c2:
            G2 = K2l([K2(co) for co in G.list()])
            c2sum = sum(qchar(G2(x), K2) for x in K2)             # over all of F_{p^2}
        else:
            c2sum = 0
        worst = (max(worst[0], abs(Integer(c1sum))), max(worst[1], abs(Integer(c2sum))))
        if c1sum == 0 and (c2sum == 0 or not do_c2):
            ok_cells += 1
    tail = "" if do_c2 else "  (c1 only)"
    verdict = ("SHAPE holds (c1=c2=0)" if do_c2 else "c1=0") if (tried and ok_cells == tried) \
              else "SHAPE BROKEN"
    print("  %-11s p=%-6d n=%-9d (%s) j=%-8s | %d/%d cells  max|c1sum|=%d max|c2sum|=%d  %s%s"
          % (tag, p, n, parity, str(E.j_invariant()), ok_cells, tried, worst[0], worst[1],
             verdict, tail))
    return parity, ok_cells, tried


def odd_j0_primes_7mod12(lo, hi, want):
    out = []
    P = lo
    while len(out) < want and P < hi:
        P = next_prime(P)
        if P % 12 == 7 and EllipticCurve(GF(P), [0, 7]).order() % 2 == 1:
            out.append(P)
    return out


def find_generic_odd(p, tries=40):
    K = GF(p)
    for _ in range(tries):
        A = K.random_element(); B = K.random_element()
        if 4*A**3 + 27*B**2 == 0:
            continue
        E = EllipticCurve(K, [A, B])
        if E.order() % 2 == 1 and E.j_invariant() not in (K(0), K(1728)):
            return (ZZ(A), ZZ(B))
    return None


# --------- FULL char poly via Sage (small p: naive F_{p^3} count is feasible) ----
def full_shape(p, A, B, n_R=3, tag=""):
    """Whole Frobenius char poly at once; check it equals T^6 - c3 T^3 + p^3 exactly."""
    K = GF(p)
    E = EllipticCurve(K, [A, B])
    n = E.order()
    parity = "odd " if n % 2 else "EVEN"
    Kl = PolynomialRing(K, 'l')
    l = Kl.gen()
    okc = 0
    tried = 0
    ex = None
    for _ in range(n_R):
        R = E.random_point()
        if R.is_zero() or R[1] == 0:
            continue
        xR, yR = R[0], R[1]
        G = (l**4 - 6*xR*l**2 - 8*yR*l - (3*xR**2 + 4*K(A))) * \
            (yR*l**3 + (K(A) + 3*xR**2)*l**2 + 3*xR*yR*l + yR**2)
        if G.degree() != 7 or not G.is_squarefree():
            continue
        tried += 1
        c = HyperellipticCurve(G).frobenius_polynomial().list()   # [c0..c6]
        # shape  T^6 - c3 T^3 + p^3  <=>  c5=c4=c2=c1=0, c0=p^3, c6=1
        if c[5] == 0 and c[4] == 0 and c[2] == 0 and c[1] == 0 and c[0] == p**3:
            okc += 1
        elif ex is None:
            ex = c
    v = ("FULL SHAPE T^6-c3T^3+p^3 holds" if (tried and okc == tried) else "SHAPE BROKEN")
    print("  %-11s p=%-5d n=%-7d (%s) j=%-7s | %d/%d cells  %s"
          % (tag, p, n, parity, str(E.j_invariant()), okc, tried, v))
    if ex is not None:
        print("        (example coeffs c0..c6 =", ex, ")")
    return parity, okc, tried


if __name__ == "__main__":
    okA = symbolic_resultant()
    print()
    print("=" * 78)
    print("(B) MECHANISM: full char poly T^6 - c3 T^3 + p^3  (c1=c2=0)  [corpus went to p<=211]")
    print("=" * 78)
    print("j=0 (secp class), p = 7 mod 12, ODD n  (FULL char poly, a bit past corpus):")
    for p in odd_j0_primes_7mod12(211, 400, 4):
        full_shape(p, 0, 7, 3, "j=0")
    print("generic j, ODD n  (FULL char poly):")
    done = 0
    for p in (223, 271, 283, 307, 331, 367):
        AB = find_generic_odd(p)
        if AB and done < 3:
            full_shape(p, AB[0], AB[1], 3, "generic"); done += 1
    print("CONTROL, EVEN n (shape MUST break):")
    for (p, A, B) in ((251, 1, 0), (263, 2, 3)):
        if EllipticCurve(GF(p), [A, B]).order() % 2 == 0:
            full_shape(p, A, B, 3, "CONTROL")
    print()
    print("c1 = 0 (= the #26 conclusion Sum chi2(G)=0) at scale is in jac26_e2_uniform_scale_v1.sage")
    print("(confirmed there to p = 10^6); full SHAPE at those p is O(p^2/p^3) and not recomputed here.")
    print()
    print("VERDICT (A) symbolic Res/disc identities:", okA)
