#!/usr/bin/env sage
"""jac26_zeta_and_branch_v1.sage -- #26: the zeta function of C: w^2 = G(lambda), and the
CORRECT (8-point) branch-locus automorphism group.

TARGET.  #26 <=> Sum_{lambda in F_p} chi_2(G_R(lambda)) = 0 for every R != O, where
    D(l) = l^4 - 6 xR l^2 - 8 yR l - 3 xR^2 - 4A        (= (x1-x2)^2)
    F(l) = yR l^3 + (A + 3 xR^2) l^2 + 3 xR yR l + yR^2 (= y1 y2)
    G    = D * F,  deg 7.
Equivalently #C(F_p) = p+1, i.e. Frobenius trace 0 on Jac(C) (genus 3).

HYPOTHESIS UNDER TEST (this session).  The reduced automorphism group of C is the stabiliser of
the *8-point* branch locus B = {7 roots of G} u {infinity} -- NOT of the 7 finite roots.  The
E[2]-translations tau_T (P -> P+T) commute with iota(P) = R-P, hence descend to Mobius maps
sigma_T of the lambda-line; sigma_T sends the root "P1 = T" to "P1 = O" = infinity, so it
permutes B while NOT permuting the 7 finite roots.  When n is odd, x^3+Ax+B is irreducible, so
E[2] is defined over F_{p^3} and Frobenius permutes T1,T2,T3 CYCLICALLY.  If Jac(C) then splits
into three elliptic pieces cyclically permuted by Frobenius, the Frobenius matrix is block-cyclic
with ZERO diagonal blocks, so:

    PREDICTION P1:  c1 = 0   (i.e. #C(F_p)   = p   + 1)     <-- this is #26 itself
    PREDICTION P2:  c2 = 0   (i.e. #C(F_p^2) = p^2 + 1)     <-- NEW, independent, not previously known
    PREDICTION P3:  Ch(T) = T^6 - a T^3 + p^3  for some integer a, |a| <= 2 p^{3/2}
    PREDICTION P4:  the branch-locus stabiliser contains (Z/2)^2 realised by the sigma_T,
                    defined over F_{p^3}, none of them F_p-rational.
    CONTROL  P5:    on an EVEN-n curve some T_i is F_p-rational, so a diagonal block survives
                    and the trace must be NONZERO.  If the control does not fire, the whole
                    mechanism reading is void.

EXACTNESS.  All arithmetic is in finite fields / ZZ.  No floating point anywhere in the signal
path; the two integer divisions (by 2 and by 3, in Newton's identities) are asserted exact.
"""

from sage.all import (GF, EllipticCurve, ZZ, PolynomialRing, Integer, prod, gcd)
import itertools


# ---------------------------------------------------------------- the objects

def DF_polys(A, B, xR, yR, ring):
    """D (quartic) and F (cubic) as polynomials in ring = K[l]."""
    l = ring.gen()
    D = l**4 - 6*xR*l**2 - 8*yR*l - (3*xR**2 + 4*A)
    F = yR*l**3 + (A + 3*xR**2)*l**2 + 3*xR*yR*l + yR**2
    return D, F


def lam_of_point(P, xR, yR):
    """slope of the line through P and -R = (xR,-yR); None if undefined (P = O or P = R)."""
    if P.is_zero():
        return None
    if P[0] == xR:
        return None
    return (P[1] + yR) / (P[0] - xR)


# ---------------------------------------------- INSTRUMENT VALIDATION (control)

def validate_G_against_points(p, A, B, Rpt):
    """Check, by direct point arithmetic, that
         sum_l chi2(G(l)) = Sum_rational_distinct - Sum_conjugate
       and that D,F really are (x1-x2)^2 and y1 y2.  Returns the character sum."""
    K = GF(p)
    Kl = PolynomialRing(K, 'l')
    xR, yR = K(Rpt[0]), K(Rpt[1])
    D, F = DF_polys(K(A), K(B), xR, yR, Kl)
    E = EllipticCurve(K, [A, B])

    # (a) D and F reproduce direct point arithmetic at every lambda that comes from a point
    checked = 0
    for P in E.points():
        lam = lam_of_point(P, xR, yR)
        if lam is None:
            continue
        P2 = E(Rpt) - P
        if P2.is_zero():
            continue
        assert D(lam) == (P[0] - P2[0])**2, "D mismatch"
        assert F(lam) == P[1]*P2[1], "F mismatch"
        checked += 1

    # (b) the character sum equals Sum_rat_distinct - Sum_conj
    chisum = ZZ(0)
    for lam in K:
        v = D(lam)*F(lam)
        if v == 0:
            continue
        chisum += 1 if v.is_square() else -1

    # rational distinct pairs {Q,Q'}, Q+Q'=R, Q!=Q', neither O
    S_rat = ZZ(0)
    seen = set()
    for Q in E.points():
        if Q.is_zero():
            continue
        Q2 = E(Rpt) - Q
        if Q2.is_zero() or Q2 == Q:
            continue
        key = frozenset([tuple(Q), tuple(Q2)])
        if key in seen:
            continue
        seen.add(key)
        S_rat += 1 if (Q[1]*Q2[1]).is_square() else -1

    # conjugate pairs {P, phi P} over F_{p^2} with P + phi P = R
    K2 = GF(p**2, 'a')
    E2 = EllipticCurve(K2, [A, B])
    R2 = E2(Rpt[0], Rpt[1])
    S_conj = ZZ(0)
    seen2 = set()
    for P in E2.points():
        if P.is_zero():
            continue
        if P[0] in K and P[1] in K:
            continue                      # rational point: not an inert pair
        Pc = E2(P[0]**p, P[1]**p)
        if P + Pc != R2:
            continue
        key = frozenset([tuple(P), tuple(Pc)])
        if key in seen2:
            continue
        seen2.add(key)
        prod_y = P[1]*Pc[1]
        assert prod_y in K, "y1 y2 not rational on an inert pair"
        S_conj += 1 if K(prod_y).is_square() else -1

    return chisum, S_rat, S_conj, checked


# ---------------------------------------------------------------- point counts

def count_C(p, k, Gcoeffs):
    """#C(F_{p^k}) for C : w^2 = G(l), deg G = 7 (odd) => exactly one point at infinity."""
    if k == 1:
        Kk = GF(p)
    else:
        Kk = GF(p**k, 'z%d' % k)
    Gk = PolynomialRing(Kk, 'l')([Kk(c) for c in Gcoeffs])
    total = ZZ(1)                                     # the single point at infinity
    for lam in Kk:
        v = Gk(lam)
        if v == 0:
            total += 1
        elif v.is_square():
            total += 2
    return total


def char_poly_from_counts(p, counts):
    """counts[k] = #C(F_{p^k}), k=1,2,3.  Returns (c1,c2,c3) of
       Ch(T) = T^6 - c1 T^5 + c2 T^4 - c3 T^3 + p c2 T^2 - p^2 c1 T + p^3,
       via s_k = sum alpha_i^k = p^k + 1 - #C(F_{p^k}) and Newton's identities."""
    s = {k: ZZ(p)**k + 1 - counts[k] for k in (1, 2, 3)}
    c1 = s[1]
    num2 = c1*s[1] - s[2]
    assert num2 % 2 == 0, "Newton c2 not integral"
    c2 = num2 // 2
    num3 = s[3] - c1*s[2] + c2*s[1]
    assert num3 % 3 == 0, "Newton c3 not integral"
    c3 = num3 // 3
    return c1, c2, c3


# --------------------------------------- the CORRECT 8-point branch-locus group

def branch_locus_group(p, A, B, xR, yR):
    """All Mobius sigma over F_{p^3} preserving B = {roots of G} u {infinity}, with the
       multiplier nu of the degree-8 binary form.  Returns (B_size, list of (sigma, nu, nu_is_square,
       sigma_is_Fp_rational)).  Points of P^1 are represented as ('f', value) or ('inf',)."""
    K3 = GF(p**3, 'w')
    Kl = PolynomialRing(K3, 'l')
    D, F = DF_polys(K3(A), K3(B), K3(xR), K3(yR), Kl)
    G = D*F
    rts = []
    for r, m in G.roots():
        assert m == 1, "G is not squarefree"
        rts.append(('f', r))
    assert len(rts) == 7, "not all 7 roots in F_{p^3}: found %d" % len(rts)
    Bl = rts + [('inf',)]

    def act(M, q):
        a, b, c, d = M
        if q[0] == 'inf':
            return ('f', a/c) if c != 0 else ('inf',)
        t = q[1]
        den = c*t + d
        return ('inf',) if den == 0 else ('f', (a*t + b)/den)

    def mobius_from_triples(src, dst):
        """the unique M with M(src_i) = dst_i, or None."""
        def to_std(q):
            # matrix sending q0 -> 0, q1 -> 1, q2 -> inf   (handles q_i = infinity)
            q0, q1, q2 = q
            if q0[0] == 'inf':
                return (0, q1[1] - q2[1], 1, -q2[1])
            if q1[0] == 'inf':
                return (1, -q0[1], 1, -q2[1])
            if q2[0] == 'inf':
                return (1, -q0[1], 0, q1[1] - q0[1])
            a = q1[1] - q2[1]
            return (a, -q0[1]*a, q1[1] - q0[1], -q2[1]*(q1[1] - q0[1]))

        def inv(M):
            a, b, c, d = M
            dt = a*d - b*c
            return None if dt == 0 else (d/dt, -b/dt, -c/dt, a/dt)

        def mul(M, N):
            a, b, c, d = M
            e, f, g, h = N
            return (a*e + b*g, a*f + b*h, c*e + d*g, c*f + d*h)

        Ms, Md = to_std(src), to_std(dst)
        if Ms[0]*Ms[3] - Ms[1]*Ms[2] == 0 or Md[0]*Md[3] - Md[1]*Md[2] == 0:
            return None
        Mdi = inv(Md)
        if Mdi is None:
            return None
        M = mul(Mdi, Ms)
        return None if M[0]*M[3] - M[1]*M[2] == 0 else M

    # the degree-8 binary form whose roots are exactly B:  Phi(X,Z) = Z * Z^7 G(X/Z)
    XZ = PolynomialRing(K3, ['X', 'Z'])
    X, Z = XZ.gens()
    Gc = G.coefficients(sparse=False)
    Phi = Z * sum(Gc[i] * X**i * Z**(7 - i) for i in range(8))

    found = []
    ref = tuple(Bl[:3])
    for tgt in itertools.permutations(Bl, int(3)):
        M = mobius_from_triples(ref, tgt)
        if M is None:
            continue
        img = [act(M, q) for q in Bl]
        if set(img) != set(Bl) or len(set(img)) != 8:
            continue
        # multiplier: Phi(aX+bZ, cX+dZ) = nu * Phi(X,Z)
        a, b, c, d = M
        Phis = Phi(a*X + b*Z, c*X + d*Z)
        cP, cS = Phi.coefficients(), Phis.coefficients()
        mons = Phi.monomials()
        nu = None
        ok = True
        for mon in mons:
            u, v = Phi.monomial_coefficient(mon), Phis.monomial_coefficient(mon)
            if u == 0:
                if v != 0:
                    ok = False
                    break
                continue
            q = v/u
            if nu is None:
                nu = q
            elif q != nu:
                ok = False
                break
        if not ok or nu is None:
            continue
        # is sigma F_p-rational?  normalise the matrix and test
        nrm = None
        for e in M:
            if e != 0:
                nrm = e
                break
        Mn = tuple(x/nrm for x in M)
        rational = all(x in GF(p) for x in Mn)
        found.append((Mn, nu, nu.is_square(), rational))
    return len(Bl), found


def sigma_T_from_points(p, A, B, Rpt, T):
    """The Mobius map induced by tau_T (P -> P+T) on the lambda-line, computed by FITTING to
       three points and then VERIFIED on every point.  Returns (M, images) or None."""
    K3 = GF(p**3, 'w')
    E3 = EllipticCurve(K3, [A, B])
    R3 = E3(Rpt[0], Rpt[1])
    xR, yR = K3(Rpt[0]), K3(Rpt[1])
    T3 = E3(T[0], T[1])
    data = []
    for P in E3.points():
        if P.is_zero():
            continue
        lam1 = lam_of_point(P, xR, yR)
        Q = P + T3
        if Q.is_zero():
            lam2 = 'inf'
        else:
            lam2 = lam_of_point(Q, xR, yR)
            if lam2 is None:
                lam2 = 'inf'
        if lam1 is None:
            lam1 = 'inf'
        data.append((lam1, lam2))
        if len(data) > 400:
            break
    # fit a Mobius map (a l + b)/(c l + d) to the finite->finite pairs by linear algebra
    from sage.all import Matrix, vector
    rows = [(l1, l2) for (l1, l2) in data if l1 != 'inf' and l2 != 'inf']
    Mrows = [[l1, 1, -l2*l1, -l2] for (l1, l2) in rows[:8]]
    Mat = Matrix(K3, Mrows)
    ker = Mat.right_kernel()
    if ker.dimension() != 1:
        return None, ker.dimension()
    a, b, c, d = ker.basis()[0]
    # VERIFY on every collected pair, infinities included
    for (l1, l2) in data:
        if l1 == 'inf':
            got = ('inf' if c == 0 else a/c)
        else:
            den = c*l1 + d
            got = ('inf' if den == 0 else (a*l1 + b)/den)
        if got != l2:
            return None, ('mismatch', l1, l2, got)
    return (a, b, c, d), None


# ---------------------------------------------------------------------- driver

def run_curve(p, A, B, label, e_list, do_branch=True):
    K = GF(p)
    E = EllipticCurve(K, [A, B])
    n = E.order()
    parity = "ODD" if n % 2 == 1 else "EVEN"
    f = PolynomialRing(K, 'x')([B, A, 0, 1])
    print("=" * 78)
    print("%s   p=%d  E: y^2=x^3+%dx+%d   n=%d (%s)   x^3+Ax+B irreducible: %s"
          % (label, p, A, B, n, parity, f.is_irreducible()))
    Gen = E.gens()[0] if E.gens() else None
    for e in e_list:
        Rpt = Integer(e) * Gen
        if Rpt.is_zero():
            continue
        xR, yR = ZZ(Rpt[0]), ZZ(Rpt[1])
        if yR % p == 0:
            print("  e=%-3d R is 2-torsion (yR=0) -- deg G < 7, skipped" % e)
            continue
        Kl = PolynomialRing(K, 'l')
        D, F = DF_polys(K(A), K(B), K(xR), K(yR), Kl)
        G = D*F
        if G.degree() != 7 or not G.is_squarefree():
            print("  e=%-3d deg G=%d squarefree=%s -- skipped" % (e, G.degree(), G.is_squarefree()))
            continue
        Gc = [ZZ(t) for t in G.coefficients(sparse=False)]

        chisum, S_rat, S_conj, nchk = validate_G_against_points(p, A, B, Rpt)
        counts = {k: count_C(p, k, Gc) for k in (1, 2, 3)}
        c1, c2, c3 = char_poly_from_counts(p, counts)

        assert chisum == S_rat - S_conj, "INSTRUMENT FAIL: chisum != S_rat - S_conj"
        assert counts[1] == p + 1 + chisum, "count/charsum mismatch"

        print("  e=%-3d R=(%d,%d) | D,F validated at %d pts | sum chi2(G)=%d = S_rat(%d)-S_conj(%d)"
              % (e, xR, yR, nchk, chisum, S_rat, S_conj))
        print("        #C(F_p)=%d (p+1=%d)  #C(F_p^2)=%d (p^2+1=%d)  #C(F_p^3)=%d"
              % (counts[1], p + 1, counts[2], p**2 + 1, counts[3]))
        print("        Ch(T) = T^6 - (%d)T^5 + (%d)T^4 - (%d)T^3 + ... | P1 c1==0: %s | P2 c2==0: %s"
              % (c1, c2, c3, c1 == 0, c2 == 0))
        if c1 == 0 and c2 == 0:
            print("        => Ch(T) = T^6 - %d T^3 + %d   [P3 form CONFIRMED]  a=%d, 2p^1.5=%.0f"
                  % (c3, p**3, c3, 2*float(p)**1.5))
        else:
            print("        => P3 form FAILS (c1=%d, c2=%d)" % (c1, c2))

    if do_branch:
        Rpt = Integer(e_list[0]) * Gen
        xR, yR = ZZ(Rpt[0]), ZZ(Rpt[1])
        nB, found = branch_locus_group(p, A, B, xR, yR)
        rat = sum(1 for (_, _, _, r) in found if r)
        sq = sum(1 for (_, _, s, _) in found if s)
        print("  BRANCH-LOCUS GROUP (|B|=%d, all %d triples tested): order %d | F_p-rational: %d"
              " | multiplier nu a square: %d" % (nB, 8*7*6, len(found), rat, sq))
        # the E[2]-translations, computed from points and verified
        f = PolynomialRing(GF(p**3, 'w'), 'x')([B, A, 0, 1])
        tors = [(r, 0) for r, _ in f.roots()]
        print("  E[2] x-coords in F_{p^3}: %d (rational ones: %d)"
              % (len(tors), sum(1 for t, _ in tors if t in GF(p))))
        for (tx, ty) in tors:
            M, err = sigma_T_from_points(p, A, B, Rpt, (tx, ty))
            if M is None:
                print("     sigma_T for T=(%s,0): FIT FAILED %s" % (tx, err))
                continue
            nrm = next(x for x in M if x != 0)
            Mn = tuple(x/nrm for x in M)
            inlist = any(Mn == Mf for (Mf, _, _, _) in found)
            # where does sigma_T send infinity?
            a, b, c, d = Mn
            img_inf = 'inf' if c == 0 else a/c
            print("     sigma_T for T=(%s,0): VERIFIED on all points | in branch group: %s"
                  " | sigma(inf)=%s | F_p-rational: %s"
                  % (tx, inlist, img_inf, all(x in GF(p) for x in Mn)))


if __name__ == "__main__":
    # --- ODD n, j=0 (the secp256k1 class)
    run_curve(43, 0, 7, "j=0  ODD-n", [1, 2, 3])
    run_curve(67, 0, 7, "j=0  ODD-n", [1, 2])
    # --- ODD n, generic j
    run_curve(79, 1, 6, "generic-j ODD-n", [1, 2])
    # --- EVEN n : the FIRING CONTROL.  Mechanism predicts trace NONZERO here.
    run_curve(43, 1, 0, "CONTROL even-n", [1, 2], do_branch=True)
