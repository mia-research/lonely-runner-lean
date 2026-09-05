#!/usr/bin/env sage
"""jac26_debug_v1.sage -- diagnose (i) the lambda-coordinate at P = -R, and (ii) why the
even-n control tripped the chisum == S_rat - S_conj instrument check.  Diagnosis only."""
from sage.all import GF, EllipticCurve, ZZ, PolynomialRing, Integer


def DF(A, B, xR, yR, ring):
    l = ring.gen()
    return (l**4 - 6*xR*l**2 - 8*yR*l - (3*xR**2 + 4*A),
            yR*l**3 + (A + 3*xR**2)*l**2 + 3*xR*yR*l + yR**2)


def diagnose(p, A, B, e):
    K = GF(p)
    E = EllipticCurve(K, [A, B])
    n = E.order()
    Gen = E.gens()[0]
    Rpt = Integer(e)*Gen
    xR, yR = K(Rpt[0]), K(Rpt[1])
    if yR == 0:
        print("  R is 2-torsion, skip")
        return
    Kl = PolynomialRing(K, 'l')
    D, F = DF(K(A), K(B), xR, yR, Kl)
    G = D*F
    print("p=%d A=%d B=%d n=%d (%s) e=%d R=(%s,%s) | ord(R)=%d | deg G=%d sqfree=%s"
          % (p, A, B, n, "odd" if n % 2 else "EVEN", e, xR, yR, Rpt.order(),
             G.degree(), G.is_squarefree()))

    # how many rational halves does R have?  (= rational roots of D)
    halves = [P for P in E.points() if 2*P == Rpt]
    print("   rational P with 2P=R: %d   | rational roots of D: %d   | rational roots of F: %d"
          % (len(halves), len(D.roots()), len(F.roots())))
    print("   rational 2-torsion pts (y=0): %d" % len([P for P in E.points()
                                                       if not P.is_zero() and P[1] == 0]))

    # build the lambda <-> pair correspondence EXPLICITLY and audit every lambda in F_p
    # lam(P) = slope of the line through P, R-P, -R.
    lam2pair = {}
    for P in E.points():
        if P.is_zero():
            continue
        P2 = Rpt - P
        if P2.is_zero():
            continue                    # the pair {O,R} -> lambda = infinity
        if P[0] == xR:
            # P = -R  (P = R is excluded above since then P2 = O): tangent at -R
            lam = -(3*xR**2 + K(A))/(2*yR)
        else:
            lam = (P[1] + yR)/(P[0] - xR)
        lam2pair.setdefault(lam, set()).add(tuple(P))

    bad = 0
    for lam, pts in sorted(lam2pair.items()):
        dv, fv = D(lam), F(lam)
        want = 1 if len(pts) == 2 else 0     # 2 rational points above lam <=> split
        if len(pts) == 1:
            # either the fixed point of iota (2P=R, so D=0) or a genuine mismatch
            if dv != 0:
                bad += 1
                print("   !! lam=%s has ONE rational point but D(lam)=%s != 0" % (lam, dv))
        else:
            if dv == 0:
                bad += 1
                print("   !! lam=%s has TWO rational points but D(lam)=0" % lam)
    print("   lambda-values realised by rational points: %d  | anomalies: %d"
          % (len(lam2pair), bad))

    # now recompute the three quantities with the CORRECTED lambda map
    chisum = ZZ(0)
    for lam in K:
        v = D(lam)*F(lam)
        if v != 0:
            chisum += 1 if v.is_square() else -1

    S_rat = ZZ(0)
    seen = set()
    for Q in E.points():
        if Q.is_zero():
            continue
        Q2 = Rpt - Q
        if Q2.is_zero() or Q2 == Q:
            continue
        key = frozenset([tuple(Q), tuple(Q2)])
        if key in seen:
            continue
        seen.add(key)
        S_rat += 1 if (Q[1]*Q2[1]).is_square() else -1

    K2 = GF(p**2, 'a')
    E2 = EllipticCurve(K2, [A, B])
    R2 = E2(Rpt[0], Rpt[1])
    S_conj = ZZ(0)
    seen2 = set()
    n_conj = 0
    for P in E2.points():
        if P.is_zero():
            continue
        if P[0] in K and P[1] in K:
            continue
        Pc = E2(P[0]**p, P[1]**p)
        if P + Pc != R2:
            continue
        key = frozenset([tuple(P), tuple(Pc)])
        if key in seen2:
            continue
        seen2.add(key)
        n_conj += 1
        S_conj += 1 if K(P[1]*Pc[1]).is_square() else -1

    print("   chisum=%d   S_rat=%d (%d pairs)   S_conj=%d (%d pairs)   chisum-(S_rat-S_conj)=%d"
          % (chisum, S_rat, len(seen), S_conj, n_conj, chisum - (S_rat - S_conj)))
    # accounting: #F_p-lambdas = #split + #inert + #(rational roots of D)
    nsplit = len(seen)
    print("   accounting: p=%d  split=%d + inert=%d + ratrootsD=%d = %d"
          % (p, nsplit, n_conj, len(D.roots()), nsplit + n_conj + len(D.roots())))


print("--- ODD-n reference (should be clean) ---")
diagnose(43, 0, 7, 1)
print("--- EVEN-n, supersingular j=1728 (the failing control) ---")
diagnose(43, 1, 0, 1)
diagnose(43, 1, 0, 2)
print("--- EVEN-n, ORDINARY generic j ---")
for (p, A, B) in [(43, 2, 3), (67, 1, 5), (79, 2, 5)]:
    E = EllipticCurve(GF(p), [A, B])
    if E.order() % 2 == 0:
        diagnose(p, A, B, 1)
