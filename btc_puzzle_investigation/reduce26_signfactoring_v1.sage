#!/usr/bin/env sage
"""reduce26_signfactoring_v1.sage -- with the CORRECT quotient t=x(P-P0), test whether chi_2(g(t)F(t))
as a function on P^1(F_p) is the restriction of a recognizable character -- i.e. is there a low-degree
polynomial h(t) with chi_2(h(t)) = chi_2(g(t)F(t)) for all t? If so, gF = h*(square), and the sum is a
classical quadratic character sum (Weil/elementary), which would be the mechanism.

Round 5 confirmed the quotient works and Sum chi_2(gF) = 0 (excl the inf diagonal). This script builds
the full sign table per R and searches for the polynomial structure.
"""
from sage.all import GF, EllipticCurve, ZZ, PolynomialRing
from collections import defaultdict


def chi2(a, p):
    a = int(a) % p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1


def sign_table(p, A, B, Rpt):
    """For fixed R, build {t in F_p : chi_2(gF)(t)} via the correct quotient t = x(P - P0)."""
    Fp = GF(p); Fp2 = GF(p**2, 'a')
    E = EllipticCurve(Fp, [A, B])
    E2 = E.change_ring(Fp2); R2 = E2(Rpt[0], Rpt[1])
    P0 = Rpt.division_points(2)[0]; P0_2 = E2(P0[0], P0[1])
    sgn = {}
    for x1 in Fp2:
        rhs = x1**3 + A*x1 + B
        if not rhs.is_square(): continue
        y1 = rhs.sqrt()
        for sgg in (1,-1):
            P = E2(x1, sgg*y1)
            if P.is_zero(): continue
            iP = R2 - P
            if iP.is_zero(): continue
            Pm = P - P0_2
            if Pm.is_zero(): continue
            if Pm[0] not in Fp: continue
            tv = int(Pm[0])
            Fv = P[1]*iP[1]
            if Fv not in Fp: continue
            inFp = (P[0] in Fp) and (P[1] in Fp)
            cg = 1 if inFp else -1
            sgn[tv] = cg * chi2(int(Fv), p)
    return sgn


if __name__ == "__main__":
    p, A, B = 43, 0, 7
    Fp = GF(p)
    E = EllipticCurve(Fp, [A, B]); n = E.order()
    G = next(P for P in E if P.order() == n)
    Ppoly = PolynomialRing(Fp, 'T'); T = Ppoly.gen()

    print("=== #26 round 5b: sign-table structure search (correct quotient) ===")
    print("p=%d. For each R, is chi_2(gF)(t) = chi_2(h(t)) for low-degree h?\n")
    for e in (1, 2, 3, 5, 7):
        Rpt = e*G
        sgn = sign_table(p, A, B, Rpt)
        if not sgn: continue
        npos = sum(1 for v in sgn.values() if v==1)
        nneg = sum(1 for v in sgn.values() if v==-1)
        print("R=[%d]G: %d t covered, +%d/-%d, sum=%d" % (e, len(sgn), npos, nneg, npos-nneg))
        # SEARCH: find low-degree h with chi_2(h(t)) == sgn[t] for all t in sgn.
        # chi_2(h(t)) for h = c*prod(t-r_i): sign is chi_2(c)*prod over roots of chi_2(t-r_i).
        # For t NOT a root, chi_2(t-r_i)=+1 if t>r_i as squares... it's chi_2 of the linear factor.
        # Brute force: try h = c*(t-a)*(t-b)*... for small degree and a constant c, check match.
        # Degree-1: h=c(t-a). chi_2(h(t))=chi_2(c)*chi_2(t-a). The set {t:chi_2(t-a)=-1} = nonsquares shifted.
        # Degree-d generic search is expensive; instead use the IDENTITY: if chi_2(gF)=chi_2(h), then
        # gF/h is a square (as a function). The "zero set" of gF (where chi_2=0) should match h's roots.
        zeros = sorted(t for t,v in sgn.items() if v==0)
        print("   zeros (chi_2=0):", zeros)
        # DEGREE-1 test first: is chi_2(gF)(t) = chi_2(c*(t-a)) for some a, c?
        # chi_2(c(t-a)) = chi_2(c)*chi_2(t-a). Match for all covered t.
        found1 = None
        nonsq = next(z for z in range(1,p) if chi2(z,p)==-1)
        for a in range(p):
            for csign in (1, -1, nonsq, (-nonsq)%p):
                if all((chi2((csign*(t-a))%p, p)) == sgn[t] for t in sgn):
                    found1 = (a, csign); break
            if found1: break
        if found1:
            a, csign = found1
            print("   *** chi_2(gF)(t) = chi_2(%d*(t-%d)) -- LINEAR structure! ***" % (csign, a))
            print("   => g(t)F(t) = %d*(t-%d) * (square in F_p(t)); Sum = Sum chi_2(t-%d) = -1 (classical)" % (csign, a, a))
            continue
        # else fall through to degree-2 search
        eta = Fp(ZZ(2))
        if not (ZZ(2).powermod((p-1)//2, p) == 1):
            nonsquares_cands = {eta, -eta}
        else:
            nonsquares_cands = {eta}
        cands = {Fp(1), Fp(-1)} | nonsquares_cands
        # Since no zeros, search h = c * (irreducible quadratics / products) of small degree.
        # Degree 2: h = c*(T^2 + aT + b). For it to have no roots (consistent with no zeros), discr nonsquare.
        found = False
        # First try h = c * (T - a)(T - b) won't work (would have roots -> zeros). So h must be
        # c*(irreducible quadratic) or c*(irreducible*cubic) etc. Try irreducible quadratics.
        for a in range(p):
            for b in range(p):
                disc = (a*a - 4*b) % p
                if disc == 0: continue
                if chi2(disc, p) == 1: continue   # reducible -> has roots -> would give zeros; skip
                h = T**2 + Fp(a)*T + Fp(b)   # irreducible quadratic
                for c in cands:
                    hc = c*h
                    if all(chi2(int(hc(t)),p) == sgn[t] for t in sgn):
                        print("   *** chi_2(gF) = chi_2(%s * (T^2+%dT+%d)) -- degree-2 structure ***" % (c, a, b))
                        found = True; break
                if found: break
            if found: break
        if not found:
            # degree-1 with no roots impossible; report no degree-2 fit
            print("   no degree-2 irreducible h matches chi_2(gF); structure (if any) is higher-degree")
        print()
