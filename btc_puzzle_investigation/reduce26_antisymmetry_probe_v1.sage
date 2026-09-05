#!/usr/bin/env sage
"""reduce26_antisymmetry_probe_v1.sage -- find the sign-reversing involution for #26.

RESULT_26_reduction_to_character_sum_v1 reduces #26 to: Sum_{t in P^1(F_p)} chi_2(g(t) F(t)) = 0 for
every R != O, where iota(P)=R-P, E/iota = P^1 via v^2=g(t) (branched at the 4 fixed points {2P=R}),
and F(t) = y_{P1} y_{P2} on the fibre. The lead: an odd symmetry (involution sigma with
chi_2(gF(sigma t)) = -chi_2(gF(t))) would force the sum to 0.

This script COMPUTES the candidates directly over F_p for small primes:
  1. The 4 branch points {P : 2P = R} (fixed points of iota) -- these define g.
  2. The quotient map E -> E/iota = P^1 concretely, via an iota-invariant coordinate.
  3. chi_2(g(t)) and chi_2(F(t)) on P^1(F_p).
  4. The E[2]-translations sigma_T (T in E[2]) as automorphisms of E/iota, and whether any is
     F_p-rational AND sign-reversing on chi_2(gF).

EXACT F_p arithmetic.
"""
from sage.all import GF, EllipticCurve, ZZ, PolynomialRing, prod, Sequence


def half_points(E, R, p):
    """The four points P with 2P = R over F_{p^2} (the branch points of E -> E/iota)."""
    # 2P = R  <=>  P is a preimage of R under [2]. Solve via the division: lift [2] and invert.
    # Concretely: P = (1/2) R in the group, but over the algebraic closure there are 4 such (the
    # coset (1/2)R + E[2]). Compute (1/2)R + each T in E[2].
    E2 = E.change_ring(GF(p**2, 'a'))
    R2 = E2(R[0], R[1])
    # find one half via division_points
    halves = R2.division_points(2)   # returns all P with 2P = R2
    return E2, halves


def iota_invariant_coordinate(E, R, p):
    """Return a function t(P) = (numerator)/(denominator), iota-invariant, as rational functions of
    (x,y) in F_p(x,y). Use t = x(P) + x(R-P) -- wait that's not invariant. Use the standard: the
    quotient by P <-> R-P identifies the two roots of the fibre. A clean invariant is the elementary
    symmetric function of the two x-coordinates in the fibre: t = x1 + x2 where P2 = R-P1.
    Concretely x(R - P1) as a function of (x1,y1), then t = x1 + x(R-P1) is iota-invariant."""
    # work symbolically? Easier: return a python function of an E(F_p^2) point.
    Rxy = (ZZ(R[0]), ZZ(R[1]))
    def t_of_P(P):
        if P.is_zero(): return None
        x1, y1 = ZZ(P[0]), ZZ(P[1])
        # P2 = R - P1. Compute via the negation+addition. -P1 = (x1, -y1). R + (-P1).
        x2, y2 = x1, (-y1) % p
        # add (R[0],R[1]) + (x2,y2) on E: y^2 = x^3 + A x + B
        A = ZZ(E.a4()); xR, yR = Rxy
        if x2 == xR:
            # P2 = R - P1 where -P1 = R => P1 = 2... degenerate; handle: if y2 == yR then R+(-P1)=2R-... skip
            return None
        lam = ((yR - y2) * pow(xR - x2, -1, p)) % p
        x3 = (lam*lam - x2 - xR) % p
        # x(R-P1) = x3 ; we don't need y3 for the INVARIANT coordinate t = x1 + x(R-P1)
        return (x1 + x3) % p
    return t_of_P


def chi2(a, p):
    a = ZZ(a) % p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1


if __name__ == "__main__":
    for (p, A, B, label) in [(43, 0, 7, "j=0 secp-class"), (79, 1, 4, "generic j"), (73, 1, 3, "generic j eps=+1")]:
        Fp = GF(p)
        E = EllipticCurve(Fp, [A, B])
        n = E.order()
        print("\n" + "="*70)
        print("p=%d  E:y^2=x^3+%dx+%d  #E=%d  (%s)" % (p, A, B, n, label))
        G = next(P for P in E if P.order() == n)
        E2 = E.change_ring(GF(p**2, 'a'))
        # test several R
        for e in (1, 2, 3, 5):
            R = e*G
            if R.is_zero(): continue
            # branch points {2P=R}
            E2R = E2(R[0], R[1])
            try:
                halves = E2R.division_points(2)
            except Exception as ex:
                print("  e=%d: division_points failed: %s" % (e, ex)); continue
            # E[2] over F_{p^2}
            E2_div2 = E2(0).division_points(2)   # E[2]: P with 2P=O
            print("  R=[%d]G : %d halves (branch pts), E[2] has %d points over F_{p^2}" % (e, len(halves), len(E2_div2)))
            # Frob action on E[2]: does any nontrivial T give an F_p-rational sigma_T?
            # sigma_T F_p-rational <=> Frob(sigma_T(t)) = sigma_T(Frob(t)) for t in P^1(F_p).
            # Simpler operational test: pick the iota-invariant coord t(P)=x1+x(R-P1); for each T in E[2],
            # check if t(P+T) is a function of t(P) over F_p (i.e. sigma_T descends F_p-rationally).
            t_of_P = iota_invariant_coordinate(E, R, p)
            # gather t-values and chi_2(gF) on the pair space directly
            # enumerate pairs {P1, R-P1} over F_{p^2} with the trace condition, compute chi_2(y1 y2) and split/inert
            seen = set(); rows = []
            for x1 in GF(p**2, 'a'):
                rhs = x1**3 + A*x1 + B
                if not rhs.is_square(): continue
                y1 = rhs.sqrt()
                for sgn in (1,-1):
                    P1 = E2(x1, sgn*y1)
                    P2 = E2R - P1
                    inFp = (P1[0] in Fp) and (P1[1] in Fp)
                    Pf = E2(P1[0]**p, P1[1]**p)
                    is_conj = (Pf == P2) and not inFp
                    is_rat_pair = inFp and (E2R - P1)[0] in Fp
                    if not (is_conj or is_rat_pair): continue
                    if P1.is_zero() or P2.is_zero(): continue
                    key = frozenset((tuple(P1), tuple(P2)))
                    if key in seen: continue
                    seen.add(key)
                    prod_y = P1[1]*P2[1]
                    assert prod_y == prod_y**p
                    cF = chi2(prod_y, p)
                    tval = t_of_P(P1)
                    rows.append((tval, is_rat_pair, cF))
            # group by t (the quotient coord); each t should have a unique chi_2(g)=split/inert and chi_2(F)
            from collections import defaultdict
            by_t = defaultdict(list)
            for tval, is_rat, cF in rows:
                by_t[tval].append((is_rat, cF))
            # for each t in the quotient, chi_2(g) = +1 if rational-split, -1 if conjugate
            sum_gF = 0; sum_cF = 0
            tlist = sorted(by_t.keys(), key=lambda z:(z is None, z))
            for tval in tlist:
                entries = by_t[tval]
                # a quotient point should be consistently split or inert
                ratts = [e for e in entries if e[0]]; conjts = [e for e in entries if not e[0]]
                cg = 1 if ratts and not conjts else (-1 if conjts and not ratts else None)
                # F-sign: for the rational case cF is chi_2(y1y2) of the single unordered pair;
                # for conjugate, same. Take the representative.
                cF_t = (ratts[0][1] if ratts else conjts[0][1])
                if cg is None: continue
                sum_gF += cg * cF_t
                sum_cF += cF_t
            print("    quotient pts: %d ; Sum chi_2(gF) = %d  (want 0); Sum chi_2(F) = %d" % (len(tlist), sum_gF, sum_cF))
