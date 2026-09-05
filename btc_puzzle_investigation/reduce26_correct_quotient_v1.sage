#!/usr/bin/env sage
"""reduce26_correct_quotient_v1.sage -- with the CORRECT quotient coordinate t = x(P - P0) (verified
1-to-1 on iota-orbits), compute g(t) and F(t) = y(P1)y(P2) as genuine elements of F_p(t), then the
proper Sum_{t in P^1(F_p)} chi_2(g(t) F(t)) and look for a factorization of gF.

Translation model: iota becomes negation on E0 = E with origin P0 = R/2. The quotient E0/<-1> = P^1
via t = x0 (x-coord in the origin-P0 model = x(P - P0)). g(t) is the cubic of E0's Weierstrass eqn;
but E0 is isomorphic to E (same j), so g is a cubic. The branch points (where the fibre degenerates)
are E0[2] = the 2-torsion of E0, i.e. x0-values of points T0 with 2 T0 = O in E0, i.e. 2(T + P0) = ... :
the branch points in original coords are {P : 2(P - P0) = O} = {P : 2P = 2P0 = R} = the half-points of R.
So g(t) = product over the 4 half-points P_h of (t - x(P_h - P0)).

F(t) = y(P1) y(P2), original y's, with {P1,P2} the fibre over t. Since P2 = R - P1 and we're on the
quotient parametrized by t = x(P1 - P0), F is a function of t.
"""
from sage.all import GF, EllipticCurve, ZZ, FunctionField, PolynomialRing


def chi2(a, p):
    a = int(a) % p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1


if __name__ == "__main__":
    p, A, B = 43, 0, 7
    Fp = GF(p); Fp2 = GF(p**2, 'a')
    E = EllipticCurve(Fp, [A, B]); n = E.order()
    G = next(P for P in E if P.order() == n)
    Rpt = 3*G; xR, yR = ZZ(Rpt[0]), ZZ(Rpt[1])
    P0 = Rpt.division_points(2)[0]
    E2 = E.change_ring(Fp2); R2 = E2(Rpt[0], Rpt[1]); P0_2 = E2(P0[0], P0[1])
    print("p=%d R=[3]G=(%d,%d) P0=R/2=(%d,%d)" % (p, xR, yR, ZZ(P0[0]), ZZ(P0[1])))

    # chi_2(g(t)) = split/inert sign of the fibre (rational pair = +1, conjugate = -1).
    # We read it directly from the orbit type rather than computing the algebraic g (which would need
    # the translated Weierstrass model; the sign is what matters).
    print("(skipping algebraic g(t) construction; using empirical split/inert sign = chi_2(g))")
    # build the FULL table: for each t in P^1(F_p), chi_2(g(t)) and chi_2(F(t)).
    # enumerate orbits (each = a t-value), record t, chi_2(g), chi_2(F=y(P1)y(P2)).
    seen_orb = set(); rows = []
    for x1 in Fp2:
        rhs = x1**3 + A*x1 + B
        if not rhs.is_square(): continue
        y1 = rhs.sqrt()
        for sg in (1,-1):
            P = E2(x1, sg*y1)
            if P.is_zero(): continue
            iP = R2 - P
            if iP.is_zero(): continue
            orb = frozenset([tuple(P), tuple(iP)])
            if orb in seen_orb: continue
            seen_orb.add(orb)
            Pm = P - P0_2
            if Pm.is_zero():
                tv = 'inf'
            else:
                xm = Pm[0]
                if xm not in Fp: continue
                tv = int(xm)
            Fv = P[1]*iP[1]
            if Fv not in Fp: continue
            Fv = int(Fv)
            # split/inert sign: rational pair (both in E(F_p)) = +1, conjugate pair = -1
            inFp = (P[0] in Fp) and (P[1] in Fp)
            is_conj = (not inFp) and (E2(P[0]**p, P[1]**p) == iP)
            cg = 1 if inFp else (-1 if is_conj else None)
            if cg is None: continue
            rows.append((tv, cg, chi2(Fv,p)))
    print("\ntotal F_p-rational orbits: %d" % len(rows))
    sum_gF = sum(cg*cF for (_,cg,cF) in rows)
    sum_gF_no_inf = sum(cg*cF for (tv,cg,cF) in rows if tv!='inf')
    print("Sum_{orbits} chi_2(g F) = %d   (excluding t=inf: %d)" % (sum_gF, sum_gF_no_inf))
    print("\nper-orbit (t, chi_2(g)=split/inert, chi_2(F), chi_2(gF)) first 16:")
    for tv, cg, cF in rows[:16]:
        print("  t=%5s : chi_2(g)=%+d chi_2(F)=%+d  => chi_2(gF)=%+d" % (tv, cg, cF, cg*cF))
    # separate the strata
    rat = [cF for (tv,cg,cF) in rows if cg==1 and tv!='inf']
    conj = [cF for (tv,cg,cF) in rows if cg==-1 and tv!='inf']
    print("\nrational-split stratum (excl inf): %d pts, sum chi_2(F) = %d" % (len(rat), sum(rat)))
    print("conjugate stratum (excl inf):      %d pts, sum chi_2(F) = %d" % (len(conj), sum(conj)))
    print("=> Sum_conj - Sum_rat = %d  (the #26 pair identity wants 0 after diagonal handling)" % (sum(conj)-sum(rat)))
