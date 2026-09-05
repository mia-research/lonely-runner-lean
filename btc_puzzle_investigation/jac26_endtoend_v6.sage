#!/usr/bin/env sage
"""jac26_endtoend_v6.sage -- the FULL chain, with the record's own definitions.

v5 [b] used a wrong reconstruction of h_2.  The definition (RESULT_26_reduction_to_character_sum_v1,
S1-S2) is a TRACE-FIBRE sum:

    h_1[d] = chi_2(y_{[d]G}),  h_1[0] = 0
    h_2[e] = SUM over P in E(F_{p^2}) with Tr(P) = P + phi(P) = [e]G  of  chi_2^{(2)}(y_P)
    V_k(a) = DFT of h_k

CHAIN TO VERIFY (each link separately, so a failure localises):
  L1  Sum_{lambda in F_p} chi_2(G_R(lambda))  ==  Sigma_rat_distinct - Sigma_conj      [the reduction]
  L2  h_2[e] == 1 + 2*Sigma_conj   and   (h_1*h_1)[e] == 1 + 2*Sigma_rat_distinct      [S2, S3]
  L3  => h_2[e] == (h_1*h_1)[e] for every e != 0                                        [#26 in convolution form]
  L4  f := h_2[0] - (h_1*h_1)[0] == -2*eps*p,  eps = chi_2(-1)                          [the diagonal]
  L5  => V_2(a) == V_1(a)^2 - 2*eps*p  for EVERY a != 0                                 [#26 in Fourier form]
  L6  => e_2(a) == e_1(a)^2 - eps*p                                                     [#26, the 120 degree law]

Run on both residues of p mod 4, j = 0 and generic j.  Exact arithmetic throughout
(finite fields, ZZ, and the cyclotomic field Q(zeta_n) for the DFT).  No floats.
"""

from sage.all import GF, EllipticCurve, ZZ, PolynomialRing, Integer, CyclotomicField


def chi2(v):
    return ZZ(0) if v == 0 else (ZZ(1) if v.is_square() else ZZ(-1))


def DF_polys(A, B, xR, yR, ring):
    l = ring.gen()
    return (l**4 - 6*xR*l**2 - 8*yR*l - (3*xR**2 + 4*A),
            yR*l**3 + (A + 3*xR**2)*l**2 + 3*xR*yR*l + yR**2)


def full_chain(p, A, B):
    K = GF(p)
    E = EllipticCurve(K, [A, B])
    n = E.order()
    if n % 2 == 0:
        return
    Gen = E.gens()[0]
    if Gen.order() != n:
        return
    eps = chi2(K(-1))
    Kl = PolynomialRing(K, 'l')

    pts = []
    P = E(0)
    for d in range(n):
        pts.append(P)
        P = P + Gen
    # NB: tuple(P) on a Sage curve point is the PROJECTIVE triple (x:y:z); index on (x,y) only.
    idx = {(pts[d][0], pts[d][1]): d for d in range(1, n)}

    h1 = [ZZ(0)]*n
    for d in range(1, n):
        h1[d] = chi2(pts[d][1])
    conv = [sum(h1[d]*h1[(e - d) % n] for d in range(n)) for e in range(n)]

    # ---- h_2 : the TRACE-FIBRE sum over E(F_{p^2})
    K2 = GF(p**2, 'a')
    E2 = EllipticCurve(K2, [A, B])
    h2 = [ZZ(0)]*n
    Sconj = [ZZ(0)]*n
    for Q in E2.points():
        if Q.is_zero():
            continue
        Qc = E2(Q[0]**p, Q[1]**p)
        Tr = Q + Qc
        yq = Q[1]
        val = ZZ(0) if yq == 0 else (ZZ(1) if yq.is_square() else ZZ(-1))
        if Tr.is_zero():
            h2[0] += val                      # the trace-zero fibre feeds e = 0
            continue
        e = idx.get((K(Tr[0]), K(Tr[1])))
        assert e is not None, "trace landed outside <G> -- E(F_p) not cyclic?"
        h2[e] += val
    # Sigma_conj per e, counted over unordered conjugate pairs
    seen = set()
    for Q in E2.points():
        if Q.is_zero() or (Q[0] in K and Q[1] in K):
            continue
        Qc = E2(Q[0]**p, Q[1]**p)
        Tr = Q + Qc
        if Tr.is_zero():
            continue
        e = idx.get((K(Tr[0]), K(Tr[1])))
        assert e is not None
        kf = frozenset([tuple(Q), tuple(Qc)])
        if kf in seen:
            continue
        seen.add(kf)
        Sconj[e] += chi2(K(Q[1]*Qc[1]))

    L1 = L2a = L2b = L3 = True
    for e in range(1, n):
        Rpt = pts[e]
        D, F = DF_polys(K(A), K(B), Rpt[0], Rpt[1], Kl)
        chisum = sum(chi2(D(l)*F(l)) for l in K)
        Srat, sn = ZZ(0), set()
        for Q in E.points():
            if Q.is_zero():
                continue
            Q2 = Rpt - Q
            if Q2.is_zero() or Q2 == Q:
                continue
            kf = frozenset([tuple(Q), tuple(Q2)])
            if kf in sn:
                continue
            sn.add(kf)
            Srat += chi2(Q[1]*Q2[1])
        if chisum != Srat - Sconj[e]:
            L1 = False
        if h2[e] != 1 + 2*Sconj[e]:
            L2a = False
        if conv[e] != 1 + 2*Srat:
            L2b = False
        if h2[e] != conv[e]:
            L3 = False

    f0 = h2[0] - conv[0]
    L4 = (f0 == -2*eps*p)

    Kc = CyclotomicField(n, 'z')
    z = Kc.gen()
    L5bad = 0
    for a in range(1, n):
        V1 = sum(h1[d]*z**((a*d) % n) for d in range(n))
        V2 = sum(h2[d]*z**((a*d) % n) for d in range(n))
        if V2 != V1**2 - 2*eps*p:
            L5bad += 1
    # L6: e_1 = -V_1, e_2 from Newton on the twisted L-poly:  V_k = -p_k
    #     p_2 = e_1^2 - 2 e_2  =>  e_2 = (e_1^2 - p_2)/2 = (V_1^2 + V_2)/2 ... use the
    #     record's convention e_2 = e_1^2 - eps*p  <=>  V_2 = V_1^2 - 2 eps p (same statement).
    print("  p=%-4d (p%%4=%d, eps=%+d)  n=%-4d j=%-8s | L1 %-5s | L2a %-5s | L2b %-5s | L3 %-5s |"
          " L4 (f0=%d vs %d) %-5s | L5 fails %d/%d"
          % (p, p % 4, eps, n, str(E.j_invariant()), L1, L2a, L2b, L3,
             f0, -2*eps*p, L4, L5bad, n - 1))
    return (L1, L2a, L2b, L3, L4, L5bad)


if __name__ == "__main__":
    print("=" * 96)
    print("THE FULL CHAIN  --  Sum chi2(G_R) = 0  ==>  #26  (e_2 = e_1^2 - chi_2(-1) p)")
    print("=" * 96)
    rows = []
    for (p, A, B) in [(43, 0, 7), (67, 0, 7), (79, 0, 7), (79, 1, 6),
                      (13, 0, 3), (37, 0, 2), (61, 0, 2), (73, 0, 2), (97, 0, 2),
                      (17, 1, 1), (29, 1, 1), (41, 1, 1), (89, 1, 1), (101, 1, 1)]:
        try:
            E = EllipticCurve(GF(p), [A, B])
        except Exception:
            continue
        if E.order() % 2 == 1:
            r = full_chain(p, A, B)
            if r:
                rows.append(r)
    print("-" * 96)
    print("SUMMARY over %d curves: L1 %d/%d | L2a %d/%d | L2b %d/%d | L3 %d/%d | L4 %d/%d |"
          " L5 total frequency failures %d"
          % (len(rows),
             sum(1 for r in rows if r[0]), len(rows),
             sum(1 for r in rows if r[1]), len(rows),
             sum(1 for r in rows if r[2]), len(rows),
             sum(1 for r in rows if r[3]), len(rows),
             sum(1 for r in rows if r[4]), len(rows),
             sum(r[5] for r in rows)))
