#!/usr/bin/env sage
"""purity_every_embedding_item6_v1.sage -- ITEM 6: discharge A3 ("purity at EVERY embedding")
by COMPUTATION rather than by citation.

THE SITUATION.  `(D2)` is used in the record for TWO different citations:
  * (D2) = STICKELBERGER  -- discharged 2026-07-27 (ADDENDUM_2 B2.1, Katre in hand, 3 caveats).
  * (D2) = WEIL II / KATZ-SARNAK sheaf purity -- still open, 4 verifier failures.
STRUCTURAL_IMPLICATIONS item G prescribes "read Ireland-Rosen Ch.14 / Berndt-Evans-Williams Ch.11".
Those are Gauss/Jacobi-sum texts -- the reading list for the STICKELBERGER (D2) (B2.1 names them as
that citation's natural follow-up).  They cannot discharge Weil II 3.2.3, which is Deligne.
The reading list is attached to the wrong (D2).

WHAT IS ACTUALLY CHECKABLE.  The record separately carries
    A3 = "purity at EVERY embedding"   [CITED], UNTESTED,
flagged load-bearing for the cap chain.  The archimedean purity was verified only as
"|root| = sqrt(p) for every a" at p = 43,67,127.  THAT IS NOT THE SAME THING: the record's own
RESULT_anew_twisted_eigenvalues_nonabelian_v1 shows the eigenvalue field is NON-ABELIAN, so the
Galois action is NOT just the relabelling a -> u*a, and varying a does not exhaust the embeddings.

THE FIX -- and it is exact.  Build
    R(T) = prod_{a=1}^{n-1} P_a(T)
where P_a is the twisted characteristic polynomial.  Each P_a has coefficients in Z[zeta_n], but the
PRODUCT over all a is Galois-stable, hence R(T) is in Z[T].  Its root set is closed under every
embedding of the splitting field.  So:

    "all roots of R have absolute value sqrt(p)"   IS   purity at every embedding,

and for R in Z[T] that is decidable EXACTLY: an even-degree P in Z[T] has all roots of modulus
sqrt(p) iff P(T) = T^m * Q(T + p/T) with Q in Z[T] of degree m having all roots REAL and in
[-2 sqrt p, 2 sqrt p].  Both conditions are exact (integrality of Q; Sturm sequence for the roots).

INPUT.  The collapse (already PROVED in the record + the #26 work) gives the twisted char poly from
e_1 alone:  e_2 = e_1^2 - eps*p,  e_3 = -p*e_1,  e_4 = p^2,  so
    P_a(T) = T^4 - e_1 T^3 + (e_1^2 - eps p) T^2 + p e_1 T + p^2,   e_1(a) = -V_1(a),
    V_1(a) = sum_d chi_2(y_{[d]G}) zeta_n^{a d}.
Nothing is assumed here beyond that collapse, which is proved, not cited.
"""

from sage.all import (GF, EllipticCurve, ZZ, QQ, CyclotomicField, PolynomialRing, RR, ComplexField)


def run(p, B=7, verbose=True):
    K = GF(p)
    E = EllipticCurve(K, [0, B])
    n = E.order()
    if n % 2 == 0 or not ZZ(n).is_prime():
        return None
    G = E.gens()[0]
    if G.order() != n:
        return None
    eps = 1 if K(-1).is_square() else -1

    # chi_2(y) along the group
    c = [0]*n
    P = E(0)
    for d in range(n):
        if d > 0:
            c[d] = 1 if K(P[1]).is_square() else -1
        P = P + G

    Kc = CyclotomicField(n, 'z')
    z = Kc.gen()
    RT = PolynomialRing(Kc, 'T')
    T = RT.gen()
    RQ = PolynomialRing(QQ, 'T')

    # the product over a of P_a, done in the cyclotomic field then coerced down
    prod_poly = RT(1)
    for a in range(1, n):
        V1 = sum(c[d]*z**((a*d) % n) for d in range(n))
        e1 = -V1
        prod_poly *= (T**4 - e1*T**3 + (e1**2 - eps*p)*T**2 + p*e1*T + p**2)
    coeffs = prod_poly.list()
    # every coefficient must be RATIONAL (Galois-stable product) -- checked, not assumed
    allrat = all(co in QQ for co in coeffs)
    if not allrat:
        return dict(p=p, n=n, ok_rat=False)
    Rfull = RQ([QQ(co) for co in coeffs])
    allint = all(QQ(co).denominator() == 1 for co in coeffs)
    # e_1 is constant on mu_6 classes, so each distinct quartic occurs SIX times in prod_a P_a.
    # Those multiplicities make (i) number_of_real_roots (distinct) < degree (with multiplicity)
    # automatically, and (ii) numerical root-finding on the full product ill-conditioned.
    # The Weil property is a property of the ROOT SET, so work with the squarefree part.
    Rq = Rfull // Rfull.gcd(Rfull.derivative())
    mult = Rfull.degree()/Rq.degree() if Rq.degree() else 0

    # exact Weil test: R(T) = T^m Q(T + p/T)
    d2 = Rq.degree()
    m = d2//2
    S = PolynomialRing(QQ, 'S').gen()
    # build Q by repeated division: express R in powers of (T + p/T)
    Rw = Rq
    Q = PolynomialRing(QQ, 'S')(0)
    ok_weil = True
    cur = Rq
    # Use the standard reduction: write R(T)/T^m as a polynomial in w = T + p/T
    Lp = PolynomialRing(QQ, 'T')
    basis = [Lp(1)]
    for k in range(1, m+1):
        # (T + p/T)^k * T^m  is a poly; build iteratively
        basis.append(basis[-1]*(Lp.gen()**2 + p))
    # match coefficients: R = sum_k q_k * T^(m-k) * (T^2+p)^k
    rem = Rq
    qs = []
    for k in range(m, -1, -1):
        term = Lp.gen()**(m-k)*(Lp.gen()**2 + p)**k
        if rem.degree() < term.degree():
            qs.append(QQ(0))
            continue
        qk = rem.leading_coefficient()/term.leading_coefficient()
        qs.append(qk)
        rem = rem - qk*term
    ok_weil = (rem == 0)
    qs = qs[::-1]
    Qpoly = PolynomialRing(QQ, 'S')(qs)
    q_int = all(QQ(x).denominator() == 1 for x in qs)
    # roots of Q must be REAL and in [-2 sqrt p, 2 sqrt p]
    nreal = Qpoly.number_of_real_roots() if Qpoly.degree() > 0 else 0
    bnd = RR(2)*RR(p).sqrt()
    rr = Qpoly.roots(RR, multiplicities=False) if Qpoly.degree() > 0 else []
    inband = all(abs(r) <= bnd + 1e-9 for r in rr)

    # independent numeric cross-check: all roots of R have |root| = sqrt(p)
    CC = ComplexField(200)
    rts = Rq.roots(CC, multiplicities=False)
    maxdev = max(abs(abs(r) - RR(p).sqrt()) for r in rts) if rts else None

    if verbose:
        print("  p=%-5d n=%-5d eps=%+d | deg R_full = %d (= 4(n-1) = %d)"
              % (p, n, eps, Rfull.degree(), 4*(n-1)))
        print("      R(T) has RATIONAL coefficients (Galois-stable product): %s" % allrat)
        print("      R(T) has INTEGER coefficients                        : %s" % allint)
        print("      R(T) = T^m Q(T + p/T) exactly (remainder 0)          : %s" % ok_weil)
        print("      Q in Z[S]                                            : %s" % q_int)
        print("      squarefree part: deg %d (full %d, uniform multiplicity %s)"
              % (Rq.degree(), Rfull.degree(), mult))
        print("      Q squarefree, all %d roots REAL: %s   all in [-2sqrt p, 2sqrt p]: %s"
              % (Qpoly.degree(), nreal == Qpoly.degree(), inband))
        print("      numeric cross-check: max ||root| - sqrt(p)| over ALL %d roots = %.3e"
              % (len(rts), maxdev))
    return dict(p=p, n=n, allrat=allrat, allint=allint, weil=ok_weil, qint=q_int,
                real=(nreal == Qpoly.degree()), band=inband, maxdev=float(maxdev))


if __name__ == "__main__":
    print("=" * 96)
    print("ITEM 6 / A3 -- purity at EVERY embedding, by exact computation (not by citation)")
    print("=" * 96)
    out = []
    for p in (43, 67, 79, 127):
        r = run(p)
        if r:
            out.append(r)
    print()
    ok = all(r["allrat"] and r["allint"] and r["weil"] and r["qint"] and r["real"] and r["band"]
             for r in out)
    print("  ALL PRIMES PASS EVERY EXACT CRITERION: %s" % ok)
    if ok:
        print("  => the twisted Frobenius eigenvalues are Weil numbers of weight 1 at EVERY embedding")
        print("     of their splitting field, verified WITHOUT invoking Weil II or Katz-Sarnak.")
    else:
        print("  => NOT established.  Do not read the conclusion; interrogate the failing criterion.")
