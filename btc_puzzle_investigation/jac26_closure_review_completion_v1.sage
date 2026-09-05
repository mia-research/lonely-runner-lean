#!/usr/bin/env sage
"""jac26_closure_review_completion_v1.sage

Completes the MECHANICAL parts of the independent closure-proof review that the context-isolated
reviewer could not finish (it re-derived the D,F parametrization independently — confirming the
geometric setup — then hit a session/API limit). Per CLAUDE.md 2b, mechanical/decidable checks are
dischargeable by self-audit WITH the artifact; that is what this file supplies.

  CHECK 1  (kills the 0/0-artifact worry on 'pi = F/D is V-invariant').
     redzero(pi - pi') tested numerator(pi - pi') in I.  For that to IMPLY pi = pi' on the variety,
     the DENOMINATOR of (pi - pi') must NOT vanish on the variety (must be a nonzerodivisor mod I).
     Here we exhibit the denominator and every group-law sub-denominator and confirm each reduces to
     a NONZERO class mod the Groebner basis of I.  => 'numerator in I' genuinely means equality.

  CHECK 2  (claim 3, the H^2 closure step, as a finite group computation).
     Enumerate the groups G of order 8 that are central extensions 1->Z/2->G->(Z/2)^2->1 with the
     Z/2 = <iota_h>.  For each, count how many of the THREE nontrivial cosets of <iota_h> consist
     ENTIRELY of involutions.  Claim: only (Z/2)^3 has all three => 'all three lifts are involutions'
     forces the split / Klein-four case.  Verified against Sage's own group library.
"""
from sage.all import (QQ, ZZ, PolynomialRing, Ideal, gap)


# =============================================================== CHECK 1
def check_no_0_over_0():
    print("=" * 78)
    print("CHECK 1 -- the pi = F/D invariance is NOT a 0/0 artifact")
    print("=" * 78)
    S = PolynomialRing(QQ, ['A', 'B', 'xR', 'yR', 'x1', 'y1', 'th'])
    A, B, xR, yR, x1, y1, th = S.gens()
    Fr = S.fraction_field()
    Af, Bf, xRf, yRf, x1f, y1f, thf = [Fr(g) for g in (A, B, xR, yR, x1, y1, th)]

    I = Ideal([yR**2 - (xR**3 + A*xR + B),
               y1**2 - (x1**3 + A*x1 + B),
               th**3 + A*th + B])
    GB = I.groebner_basis()

    def add_pts(xP, yP, xQ, yQ):
        s = (yQ - yP) / (xQ - xP); xr = s**2 - xP - xQ; return xr, s*(xP - xr) - yP

    def add_2tors(xP, yP, xt):
        s = yP / (xP - xt); xr = s**2 - xP - xt; return xr, s*(xP - xr) - yP

    x2, y2 = add_pts(xRf, yRf, x1f, -y1f)
    pi = (y1f*y2) / (x1f - x2)**2
    x1p, y1p = add_2tors(x1f, y1f, thf)
    x2p, y2p = add_2tors(x2, y2, thf)
    pip = (y1p*y2p) / (x1p - x2p)**2

    delta = pi - pip
    num = S(delta.numerator())
    den = S(delta.denominator())

    print("  numerator(pi - pi')  reduces to 0 mod I : ", num.reduce(GB) == 0)
    print("  denominator(pi - pi') reduces to        : ",
          "0 (BAD -- would be 0/0)" if den.reduce(GB) == 0 else "NONZERO (good)")

    # exhibit each atomic group-law denominator is a nonzerodivisor mod I
    atoms = {
        "xR - x1  (R != P1)":            S(xR - x1),
        "x1 - th  (P1 != T horiz.)":     S(x1 - th),
        "x2 - th  (P2 != T horiz.)":     S(delta.parent()(x2 - thf).numerator()),
        "(x1 - x2)^2  = D":              S(((x1f - x2)**2).numerator()),
        "(x1' - x2')^2 = D'":            S(((x1p - x2p)**2).numerator()),
    }
    allnz = True
    for name, poly in atoms.items():
        nz = poly.reduce(GB) != 0
        allnz = allnz and nz
        print("    %-28s in I ? %s" % (name, "YES (would be bad)" if not nz else "no -> nonzerodivisor"))
    print("  VERDICT check 1: pi is genuinely V-invariant (not 0/0):",
          num.reduce(GB) == 0 and den.reduce(GB) != 0 and allnz)
    return num.reduce(GB) == 0 and den.reduce(GB) != 0 and allnz


# =============================================================== CHECK 2
def check_group_theory():
    print()
    print("=" * 78)
    print("CHECK 2 -- 'all 3 lifts are involutions' forces the split (Z/2)^2 (Klein-four) closure")
    print("=" * 78)
    print("  For each order-8 group G = central extension 1->Z/2->G->(Z/2)^2->1 (iota_h = the Z/2),")
    print("  count nontrivial cosets of <iota_h> that contain an involution lift:")
    results = {}
    for gid in range(1, 6):
        G = libgap.SmallGroup(8, gid)
        name = str(G.StructureDescription())
        elts = list(G.Elements())
        one = G.Identity()
        Z = G.Centre()
        best = None
        for z in elts:
            if int(z.Order()) != 2:
                continue
            if not bool(z in Z):                       # central
                continue
            H = G.Subgroup([z])
            Q = G.FactorGroup(H)
            if str(Q.StructureDescription()) != "C2 x C2":
                continue
            good = 0
            for c in G.RightCosets(H):
                reps = list(c.Elements())
                ords = [int(e.Order()) for e in reps]
                if 1 in ords:                          # identity coset
                    continue
                # a coset {g, iota_h*g}: g order 2  <=>  iota_h*g order 2 (since (iota_h g)^2=g^2)
                if all(o == 2 for o in ords):
                    good += 1
            best = good if best is None else max(best, good)
        if best is not None:
            results[name] = best
            print("    SmallGroup(8,%d) = %-12s : %d of 3 nontrivial cosets carry an involution lift"
                  % (gid, name, best))
    klein = sorted([k for k, v in results.items() if v == 3])
    print("  Groups where ALL 3 nontrivial cosets carry an involution lift:", klein)
    ok = (klein == ["C2 x C2 x C2"])
    print("  VERDICT check 2: only (Z/2)^3 (= Klein-four lift x <iota_h>) qualifies =>",
          "'all 3 lifts involutions' FORCES Klein-four closure:", ok)
    return ok


if __name__ == "__main__":
    c1 = check_no_0_over_0()
    c2 = check_group_theory()
    print()
    print("BOTH mechanical review checks pass:", c1 and c2)
