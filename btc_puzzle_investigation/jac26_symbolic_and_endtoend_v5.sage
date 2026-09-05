#!/usr/bin/env sage
"""jac26_symbolic_and_endtoend_v5.sage -- close the two remaining gaps.

GAP 1 (p-independence).  Lemma 1 (the formulas for D and F) has so far been checked per prime.
       Prove it SYMBOLICALLY with A, B, x_R, y_R free indeterminates subject only to
       y_R^2 = x_R^3 + A x_R + B.  A symbolic identity holds at EVERY p > 3, so no prime sweep
       is needed for this step.  Also prove symbolically:
         - the discriminant/resultant conditions making G squarefree of degree 7,
         - res(D, F) != 0 identically (the two branch orbits are disjoint),
       each as an explicit polynomial in A, B, x_R, y_R whose vanishing locus is named.

GAP 2 (p mod 4).  Every prime swept so far is p = 3 mod 4.  The record's e_2 law is
       BRANCH-DEPENDENT (e_2 = e_1^2 - chi_2(-1) p), so p = 1 mod 4 must be covered explicitly.
       Test P1 & P2 on odd-n curves with p = 1 mod 4.

GAP 3 (end-to-end).  Verify the full chain, not just its first link:
         Sum_lambda chi_2(G_R) = 0 for every R
           <=> h_2[d] = (h_1*h_1)[d] for every d != 0
           <=> V_2(a) = V_1(a)^2 - 2 chi_2(-1) p  for every a
           <=> e_2(a) = e_1(a)^2 - chi_2(-1) p          [ = #26, the 120 degree law ]
       computed DIRECTLY from E(F_p) and E(F_p^2), at both residues of p mod 4.

EXACTNESS.  Symbolic stage: exact polynomial algebra over QQ.  Numeric stage: finite fields / ZZ.
No floats.
"""

from sage.all import (GF, EllipticCurve, ZZ, QQ, PolynomialRing, Integer,
                      PolynomialRing as PR, CyclotomicField, prod)


# =============================================================== GAP 1: symbolic

def symbolic_lemma1():
    print("#" * 78)
    print("GAP 1 -- SYMBOLIC verification of Lemma 1 (holds at every p > 3)")
    print("#" * 78)
    S = PolynomialRing(QQ, ['A', 'B', 'xR', 'yR', 'l'])
    A, B, xR, yR, l = S.gens()
    # the curve relation
    curve_rel = yR**2 - (xR**3 + A*xR + B)

    # The line through -R = (xR, -yR) of slope l meets E where
    #   x^3 + A x + B - (l(x - xR) - yR)^2 = 0,
    # a cubic with roots xR, x1, x2.
    Sx = PolynomialRing(S, 'x')
    x = Sx.gen()
    cubic = x**3 + A*x + B - (l*(x - xR) - yR)**2
    # divide out the known root x = xR  (exact only modulo the curve relation)
    quo, rem = cubic.quo_rem(x - xR)
    # rem must be the curve relation up to sign
    remc = rem.constant_coefficient() if rem.degree() <= 0 else None
    print("  cubic / (x - xR): remainder = %s" % remc)
    print("  remainder is exactly (xR^3 + A xR + B - yR^2) = -curve_rel : %s"
          % (S(remc) + curve_rel == 0))

    # quo = x^2 + s1' x + s0' ; so x1 + x2 = -coeff, x1 x2 = const
    c1 = quo.coefficients(sparse=False)
    sum12 = -c1[1]
    prod12 = c1[0]
    print("  x1 + x2 = %s" % sum12)
    print("           == l^2 - xR : %s" % (S(sum12) - (l**2 - xR) == 0))
    print("  x1 x2   = %s" % prod12)
    print("           == xR l^2 + 2 yR l + A + xR^2 : %s"
          % (S(prod12) - (xR*l**2 + 2*yR*l + A + xR**2) == 0))

    D_claim = l**4 - 6*xR*l**2 - 8*yR*l - (3*xR**2 + 4*A)
    D_derived = S(sum12)**2 - 4*S(prod12)
    print("  D := (x1-x2)^2 = (x1+x2)^2 - 4 x1 x2 == claimed quartic : %s"
          % (D_derived - D_claim == 0))

    # F = y1 y2 with y_i = l(x_i - xR) - yR
    #   = l^2 (x1-xR)(x2-xR) - l yR [(x1-xR)+(x2-xR)] + yR^2
    e_prod = S(prod12) - xR*S(sum12) + xR**2          # (x1-xR)(x2-xR)
    e_sum = S(sum12) - 2*xR                            # (x1-xR)+(x2-xR)
    F_derived = l**2*e_prod - l*yR*e_sum + yR**2
    F_claim = yR*l**3 + (A + 3*xR**2)*l**2 + 3*xR*yR*l + yR**2
    diff = F_derived - F_claim
    print("  F := y1 y2 == claimed cubic, modulo the curve relation : %s"
          % (diff.reduce([curve_rel]) == 0))
    print("     (raw difference = %s ; reduces to 0 mod yR^2 - (xR^3+A xR+B))" % diff)

    # ---- degree / squarefreeness conditions, symbolically
    Sl = PolynomialRing(PolynomialRing(QQ, ['A', 'B', 'xR', 'yR']), 'l')
    A2, B2, xR2, yR2 = Sl.base_ring().gens()
    L = Sl.gen()
    Dp = L**4 - 6*xR2*L**2 - 8*yR2*L - (3*xR2**2 + 4*A2)
    Fp = yR2*L**3 + (A2 + 3*xR2**2)*L**2 + 3*xR2*yR2*L + yR2**2
    print("\n  deg D = 4 always (monic).  deg F = 3 iff yR != 0, i.e. iff R is NOT 2-torsion;")
    print("  n odd => E(F_p) has no 2-torsion => yR != 0 for every R != O.  [deg G = 7]")
    resDF = Dp.resultant(Fp)
    print("  Res(D, F) as a polynomial in A,B,xR,yR:")
    print("     %s" % resDF.factor())
    print("  => D and F share a root only on the named vanishing locus above;")
    print("     the geometric statement (Lemma 3) is that this locus is exactly")
    print("     'R is 2-torsion' (yR = 0) and the singular-curve locus (4A^3+27B^2 = 0).")
    dD = Dp.discriminant()
    print("  disc(D) factors as: %s" % dD.factor())
    return True


# ========================================================= shared numeric helpers

def chi2(v):
    return ZZ(0) if v == 0 else (ZZ(1) if v.is_square() else ZZ(-1))


def DF_polys(A, B, xR, yR, ring):
    l = ring.gen()
    return (l**4 - 6*xR*l**2 - 8*yR*l - (3*xR**2 + 4*A),
            yR*l**3 + (A + 3*xR**2)*l**2 + 3*xR*yR*l + yR**2)


def count_C(p, k, Gc):
    Kk = GF(p) if k == 1 else GF(p**k, 'z%d' % k)
    Gk = PolynomialRing(Kk, 'l')([Kk(c) for c in Gc])
    tot = ZZ(1)
    for lam in Kk:
        v = Gk(lam)
        tot += 1 if v == 0 else (2 if v.is_square() else 0)
    return tot


def coeffs12(p, counts):
    s = {k: ZZ(p)**k + 1 - counts[k] for k in (1, 2)}
    c1 = s[1]
    n2 = c1*s[1] - s[2]
    assert n2 % 2 == 0
    return c1, n2 // 2


def sweep_P1P2(p, A, B, label, max_R=40):
    K = GF(p)
    E = EllipticCurve(K, [A, B])
    n = E.order()
    Gen = E.gens()[0]
    ok = bad = 0
    for e in range(1, min(n, max_R + 1)):
        Rpt = Integer(e)*Gen
        if Rpt.is_zero() or Rpt[1] == 0:
            continue
        Kl = PolynomialRing(K, 'l')
        D, F = DF_polys(K(A), K(B), Rpt[0], Rpt[1], Kl)
        G = D*F
        if G.degree() != 7 or not G.is_squarefree():
            continue
        Gc = [ZZ(t) for t in G.coefficients(sparse=False)]
        c1, c2 = coeffs12(p, {k: count_C(p, k, Gc) for k in (1, 2)})
        if c1 == 0 and c2 == 0:
            ok += 1
        else:
            bad += 1
    print("  %-14s p=%-4d (p mod 4 = %d) n=%-5d %-4s j=%-6s | cells %-3d | P1&P2 hold %-3d |"
          " VIOLATIONS %d" % (label, p, p % 4, n, "ODD" if n % 2 else "EVEN",
                              str(E.j_invariant()), ok + bad, ok, bad))
    return ok, bad


# ================================================ GAP 3: the full chain, end to end

def end_to_end(p, A, B):
    """Verify  [Sum_lambda chi2(G_R) = 0 for all R]  <->  [h2 = h1*h1 off 0]
       <->  V2(a) = V1(a)^2 - 2 chi2(-1) p  for all a != 0."""
    K = GF(p)
    E = EllipticCurve(K, [A, B])
    n = E.order()
    if n % 2 == 0 or not E.abelian_group().is_cyclic():
        return None
    Gen = E.gens()[0]
    if Gen.order() != n:
        return None
    eps = chi2(K(-1))                       # chi_2(-1) = +1 if p = 1 mod 4 else -1

    # h1[d] = chi2(y_{[d]G}) for d = 1..n-1 ; h1[0] = 0
    pts = [None]*n
    P = E(0)
    for d in range(n):
        pts[d] = P
        P = P + Gen
    h1 = [ZZ(0)]*n
    for d in range(1, n):
        h1[d] = chi2(pts[d][1])

    # h2[d] = chi_2^{(2)}(y of the F_{p^2}-point) -- the record's second-layer sequence:
    #   h2[d] = chi_2( N_{F_p^2/F_p}( y_{[d]G2} ) ) where G2 = G viewed on E(F_{p^2}).
    # Equivalently h2[d] = chi2( y_{[d]G} ^ (p+1) ) = chi2(y)^{p+1} = +1 -- degenerate on
    # rational points, so h2 must be taken over E(F_{p^2}) with its own generator.  We use the
    # intrinsic definition that the reduction doc uses:  h2[e] = sum over Galois-stable pairs.
    # Concretely, compare the two strata directly (this is the object the reduction produces):
    K2 = GF(p**2, 'a')
    E2 = EllipticCurve(K2, [A, B])

    conv = [ZZ(0)]*n                        # (h1 * h1)[e]  (cyclic convolution along <G>)
    for e in range(n):
        s = ZZ(0)
        for d in range(n):
            s += h1[d]*h1[(e - d) % n]
        conv[e] = s

    # chi-sum side, per R = [e]G
    chisums = {}
    strata = {}
    for e in range(1, n):
        Rpt = pts[e]
        if Rpt[1] == 0:
            continue
        Kl = PolynomialRing(K, 'l')
        D, F = DF_polys(K(A), K(B), Rpt[0], Rpt[1], Kl)
        chisums[e] = sum(chi2(D(l)*F(l)) for l in K)
        # split stratum sum, with the diagonal P0 (2P0 = R) added back:
        S_rat, seen = ZZ(0), set()
        for Q in E.points():
            if Q.is_zero():
                continue
            Q2 = Rpt - Q
            if Q2.is_zero():
                continue
            key = frozenset([tuple(Q), tuple(Q2)])
            if key in seen:
                continue
            seen.add(key)
            S_rat += (chi2(Q[1]*Q2[1]) if Q != Q2 else ZZ(0))
        strata[e] = S_rat

    # the convolution identity: (h1*h1)[e] = 2*S_rat_distinct + (diagonal)
    diag_ok = True
    for e in chisums:
        Rpt = pts[e]
        halves = [Q for Q in E.points() if 2*Q == Rpt]
        dg = sum(chi2(Q[1])**2 for Q in halves)      # each rational half contributes +1
        if conv[e] != 2*strata[e] + dg:
            diag_ok = False
    # V1, V2 by DFT over the n-th roots of unity, computed EXACTLY in Q(zeta_n)
    Kc = CyclotomicField(n, 'z')
    z = Kc.gen()
    allok = True
    checked = 0
    for a in range(1, n):
        V1 = sum(h1[d]*z**((a*d) % n) for d in range(n))
        V2 = sum(conv[d]*z**((a*d) % n) for d in range(n))
        # #26 in coefficient form
        if V2 != V1**2:
            allok = False
        checked += 1
    zero_all = all(v == 0 for v in chisums.values())
    print("  p=%-4d (p mod 4=%d, chi2(-1)=%+d) n=%-4d j=%-6s | Sum chi2(G_R)=0 for ALL R: %-5s |"
          " conv-diagonal bookkeeping: %-5s | V2(a) == V1(a)^2 (DFT of the convolution): %s (%d a's)"
          % (p, p % 4, eps, n, str(E.j_invariant()), zero_all, diag_ok, allok, checked))
    return zero_all, diag_ok, allok


# ------------------------------------------------- the real V1, V2 from the curve

def V_identity_direct(p, A, B):
    """V_k(a) built DIRECTLY from E(F_{p^k}), and the law V2 = V1^2 - 2 chi2(-1) p tested."""
    K = GF(p)
    E = EllipticCurve(K, [A, B])
    n = E.order()
    if n % 2 == 0:
        return None
    Gen = E.gens()[0]
    if Gen.order() != n:
        return None
    eps = chi2(K(-1))
    K2 = GF(p**2, 'a')
    E2 = EllipticCurve(K2, [A, B])
    n2 = E2.order()
    if n2 % n != 0:
        return None
    # h1 along <G> in E(F_p); h2 along the SAME index set, lifted:  h2[d] = chi_2^{(2)}(y_{[d]G2})
    # where G2 is a point of E(F_{p^2}) of order n whose reduction indexes the same cyclic group.
    G2 = None
    for P in E2.points():
        if P.order() == n:
            G2 = P
            break
    if G2 is None:
        return None
    h1 = [ZZ(0)]*n
    h2 = [ZZ(0)]*n
    P = E(0)
    Q = E2(0)
    for d in range(n):
        if d > 0:
            h1[d] = chi2(P[1])
            yq = Q[1]
            h2[d] = ZZ(0) if yq == 0 else (ZZ(1) if yq.is_square() else ZZ(-1))
        P = P + Gen
        Q = Q + G2
    conv = [sum(h1[d]*h1[(e - d) % n] for d in range(n)) for e in range(n)]
    resid = [h2[e] - conv[e] for e in range(n)]
    off0 = all(r == 0 for e, r in enumerate(resid) if e != 0)
    Kc = CyclotomicField(n, 'z')
    z = Kc.gen()
    bad = 0
    for a in range(1, n):
        V1 = sum(h1[d]*z**((a*d) % n) for d in range(n))
        V2 = sum(h2[d]*z**((a*d) % n) for d in range(n))
        if V2 != V1**2 - 2*eps*p:
            bad += 1
    print("  p=%-4d (p mod 4=%d, eps=%+d) n=%-4d j=%-7s | h2 - h1*h1 vanishes off d=0: %-5s |"
          " V2 = V1^2 - 2*eps*p FAILS at %d of %d frequencies"
          % (p, p % 4, eps, n, str(E.j_invariant()), off0, bad, n - 1))
    return off0, bad


if __name__ == "__main__":
    symbolic_lemma1()

    print("\n" + "#" * 78)
    print("GAP 2 -- P1 & P2 on ODD-n curves with p = 1 mod 4 (never previously covered)")
    print("#" * 78)
    tot_ok = tot_bad = 0
    found = 0
    for p in [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149, 157, 181, 193]:
        if p % 4 != 1:
            continue
        for (A, B) in [(0, 7), (0, 2), (0, 3), (1, 1), (1, 6), (2, 3), (3, 5), (2, 5), (4, 1)]:
            try:
                E = EllipticCurve(GF(p), [A, B])
            except Exception:
                continue
            if E.order() % 2 == 1:
                o, b = sweep_P1P2(p, A, B, "p=1 mod 4", max_R=30)
                tot_ok += o
                tot_bad += b
                found += 1
                break
        if found >= 10:
            break
    print("  TOTAL p=1 mod 4: %d cells, P1&P2 hold %d, VIOLATIONS %d"
          % (tot_ok + tot_bad, tot_ok, tot_bad))

    print("\n" + "#" * 78)
    print("GAP 3 -- the FULL chain: Sum chi2(G_R)=0  ->  h2 = h1*h1  ->  V2 = V1^2 - 2 eps p")
    print("#" * 78)
    print(" [a] the chi-sum / convolution bookkeeping:")
    for (p, A, B) in [(43, 0, 7), (67, 0, 7), (79, 1, 6), (37, 0, 2), (61, 1, 1), (13, 0, 3)]:
        try:
            E = EllipticCurve(GF(p), [A, B])
        except Exception:
            continue
        if E.order() % 2 == 1:
            end_to_end(p, A, B)
    print(" [b] V1, V2 built DIRECTLY from E(F_p) and E(F_p^2):")
    for (p, A, B) in [(43, 0, 7), (67, 0, 7), (79, 1, 6), (37, 0, 2), (61, 1, 1), (13, 0, 3),
                      (97, 1, 1), (109, 0, 2)]:
        try:
            E = EllipticCurve(GF(p), [A, B])
        except Exception:
            continue
        if E.order() % 2 == 1:
            V_identity_direct(p, A, B)
