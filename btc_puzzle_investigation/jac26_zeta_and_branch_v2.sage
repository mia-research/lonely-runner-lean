#!/usr/bin/env sage
"""jac26_zeta_and_branch_v2.sage -- #26 via the genus-3 curve C: w^2 = G(lambda).

FIXES vs v1 (both found by controls, both recorded):
  (1) chi2(0) must be 0.  Sage's `0.is_square()` is True, so v1's S_rat scored a pair with
      y1*y2 = 0 as +1.  Only reachable when E has rational 2-torsion, i.e. n EVEN -- which is
      why the odd-n arm was unaffected and the even-n control caught it.
  (2) lambda(P) at P = -R is the TANGENT slope at -R, not undefined.  lambda = infinity is the
      single orbit {O, R} only.

WHAT THIS TESTS.  See v1 header for the mechanism.  Predictions:
  P1  c1 = 0        (#C(F_p)   = p+1)      <-- #26 itself
  P2  c2 = 0        (#C(F_p^2) = p^2+1)    <-- independent consequence of the cyclic-block shape
  P3  Ch(T) = T^6 - a T^3 + p^3
  P4  the 8-point branch-locus stabiliser is (Z/2)^2, realised by the E[2]-translations
      sigma_T, defined over F_{p^3}, none F_p-rational, each acting on the 8-point locus B as
      FOUR TRANSPOSITIONS (fixed-point-free): it swaps infinity with the F-root lambda_T, swaps
      the other two F-roots, and acts on D's four roots as translation by T.
  P5  CONTROL, even n: one T is F_p-rational => one sigma_T is F_p-rational => a Frobenius
      diagonal block survives => trace NONZERO.  If this does not fire, the reading is void.
  P6  the lifts sigma~_T have quotient genera {1, 2} (the two lifts), and Frobenius permutes
      the three sigma_T CYCLICALLY when n is odd.

EXACTNESS.  Finite-field / ZZ arithmetic only.  The two Newton divisions (by 2, by 3) are
asserted exact.  The single float in the file is a display-only Hasse-bound printout.
"""

from sage.all import (GF, EllipticCurve, ZZ, PolynomialRing, Integer, Set)
import itertools


# ------------------------------------------------------------------ primitives

def chi2(v):
    """quadratic character, with chi2(0) = 0.  (Sage's 0.is_square() is True -- v1's bug.)"""
    if v == 0:
        return ZZ(0)
    return ZZ(1) if v.is_square() else ZZ(-1)


def DF_polys(A, B, xR, yR, ring):
    l = ring.gen()
    return (l**4 - 6*xR*l**2 - 8*yR*l - (3*xR**2 + 4*A),
            yR*l**3 + (A + 3*xR**2)*l**2 + 3*xR*yR*l + yR**2)


def lam_of(P, Rpt, A):
    """lambda(P) = slope of the line through P, R-P, -R.  Returns None for lambda = infinity,
       which happens exactly on the orbit {O, R}.  At P = -R the line is the TANGENT at -R."""
    if P.is_zero() or P == Rpt:
        return None
    xR, yR = Rpt[0], Rpt[1]
    if P[0] == xR:                     # P = -R
        return -(3*xR**2 + A)/(2*yR)
    return (P[1] + yR)/(P[0] - xR)


# ------------------------------------------------ instrument validation (control)

def validate(p, A, B, Rpt):
    """chi-sum vs the two Frobenius strata, computed independently by point arithmetic."""
    K = GF(p)
    Kl = PolynomialRing(K, 'l')
    xR, yR = K(Rpt[0]), K(Rpt[1])
    D, F = DF_polys(K(A), K(B), xR, yR, Kl)
    E = EllipticCurve(K, [A, B])

    nchk = 0
    for P in E.points():
        lam = lam_of(P, Rpt, K(A))
        if lam is None:
            continue
        P2 = Rpt - P
        if P2.is_zero():
            continue
        assert D(lam) == (P[0] - P2[0])**2, "D mismatch at %s" % P
        assert F(lam) == P[1]*P2[1], "F mismatch at %s" % P
        nchk += 1

    chisum = sum(chi2(D(l)*F(l)) for l in K)

    S_rat, seen = ZZ(0), set()
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
        S_rat += chi2(Q[1]*Q2[1])

    K2 = GF(p**2, 'a')
    E2 = EllipticCurve(K2, [A, B])
    R2 = E2(Rpt[0], Rpt[1])
    S_conj, seen2 = ZZ(0), set()
    for P in E2.points():
        if P.is_zero() or (P[0] in K and P[1] in K):
            continue
        Pc = E2(P[0]**p, P[1]**p)
        if P + Pc != R2:
            continue
        key = frozenset([tuple(P), tuple(Pc)])
        if key in seen2:
            continue
        seen2.add(key)
        S_conj += chi2(K(P[1]*Pc[1]))
    return chisum, S_rat, S_conj, nchk, len(seen), len(seen2)


# ---------------------------------------------------------------- point counts

def count_C(p, k, Gc):
    """#C(F_{p^k}) for w^2 = G, deg G = 7 odd => exactly one point at infinity."""
    Kk = GF(p) if k == 1 else GF(p**k, 'z%d' % k)
    Gk = PolynomialRing(Kk, 'l')([Kk(c) for c in Gc])
    tot = ZZ(1)
    for lam in Kk:
        v = Gk(lam)
        tot += 1 if v == 0 else (2 if v.is_square() else 0)
    return tot


def char_poly_coeffs(p, counts):
    s = {k: ZZ(p)**k + 1 - counts[k] for k in (1, 2, 3)}
    c1 = s[1]
    n2 = c1*s[1] - s[2]
    assert n2 % 2 == 0, "Newton c2 not integral"
    c2 = n2 // 2
    n3 = s[3] - c1*s[2] + c2*s[1]
    assert n3 % 3 == 0, "Newton c3 not integral"
    return c1, c2, n3 // 3


# ------------------------------------------- the 8-point branch locus and its group

class P1pt(object):
    """a point of P^1: ('f', v) or ('inf',) -- hashable, comparable."""
    pass


def act(M, q):
    a, b, c, d = M
    if q[0] == 'inf':
        return ('f', a/c) if c != 0 else ('inf',)
    den = c*q[1] + d
    return ('inf',) if den == 0 else ('f', (a*q[1] + b)/den)


def _to_std(q):
    q0, q1, q2 = q
    if q0[0] == 'inf':
        return (0, q1[1] - q2[1], 1, -q2[1])
    if q1[0] == 'inf':
        return (1, -q0[1], 1, -q2[1])
    if q2[0] == 'inf':
        return (1, -q0[1], 0, q1[1] - q0[1])
    a = q1[1] - q2[1]
    return (a, -q0[1]*a, q1[1] - q0[1], -q2[1]*(q1[1] - q0[1]))


def _inv(M):
    a, b, c, d = M
    dt = a*d - b*c
    return None if dt == 0 else (d/dt, -b/dt, -c/dt, a/dt)


def _mul(M, N):
    a, b, c, d = M
    e, f, g, h = N
    return (a*e + b*g, a*f + b*h, c*e + d*g, c*f + d*h)


def _norm(M):
    nrm = next(x for x in M if x != 0)
    return tuple(x/nrm for x in M)


def mobius_from(src, dst):
    Ms, Md = _to_std(src), _to_std(dst)
    if Ms[0]*Ms[3] - Ms[1]*Ms[2] == 0 or Md[0]*Md[3] - Md[1]*Md[2] == 0:
        return None
    Mdi = _inv(Md)
    if Mdi is None:
        return None
    M = _mul(Mdi, Ms)
    return None if M[0]*M[3] - M[1]*M[2] == 0 else M


def branch_group(p, A, B, Rpt):
    """Exhaustive over F-bar: every Mobius map preserving B = roots(G) u {infinity}.
       Returns (Bl, Droots, Froots, found) with found = [(M_normalised, nu, nu_is_square, Fp_rational)]."""
    K3 = GF(p**3, 'w')
    Kl = PolynomialRing(K3, 'l')
    D, F = DF_polys(K3(A), K3(B), K3(Rpt[0]), K3(Rpt[1]), Kl)
    G = D*F
    Dr = [('f', r) for r, m in D.roots() for _ in range(m)]
    Fr = [('f', r) for r, m in F.roots() for _ in range(m)]
    rts = [('f', r) for r, m in G.roots()]
    if len(rts) != 7:
        # expected when n is EVEN: E[2] is not the full F_{p^3} object, so G does not split there.
        # Not an error -- the branch-locus group is only claimed for the odd-n case.
        return None, None, None, None
    Bl = rts + [('inf',)]

    XZ = PolynomialRing(K3, ['X', 'Z'])
    X, Z = XZ.gens()
    Gc = G.coefficients(sparse=False)
    Phi = Z * sum(Gc[i] * X**i * Z**(7 - i) for i in range(8))

    found, seen = [], set()
    ref = tuple(Bl[:3])
    for tgt in itertools.permutations(Bl, int(3)):
        M = mobius_from(ref, tgt)
        if M is None:
            continue
        if set(act(M, q) for q in Bl) != set(Bl):
            continue
        Mn = _norm(M)
        if Mn in seen:
            continue
        seen.add(Mn)
        a, b, c, d = M
        Phis = Phi(a*X + b*Z, c*X + d*Z)
        nu, ok = None, True
        for mon in Phi.monomials():
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
        found.append((Mn, nu, nu.is_square(), all(x in GF(p) for x in Mn)))
    return Bl, Dr, Fr, found


def sigma_T(p, A, B, Rpt, Tx):
    """The Mobius map induced by tau_T (P -> P+T), T = (Tx,0), FITTED from three points and
       then VERIFIED on every point of E(F_{p^3}) (infinities included)."""
    K3 = GF(p**3, 'w')
    E3 = EllipticCurve(K3, [A, B])
    R3 = E3(Rpt[0], Rpt[1])
    T3 = E3(Tx, K3(0))
    pairs = []
    for P in E3.points():
        l1 = lam_of(P, R3, K3(A))
        l2 = lam_of(P + T3, R3, K3(A))
        pairs.append((('inf',) if l1 is None else ('f', l1),
                      ('inf',) if l2 is None else ('f', l2)))
    # fit from three source points with distinct images
    M = None
    for i in range(len(pairs)):
        for j in range(i + 1, len(pairs)):
            for k in range(j + 1, len(pairs)):
                src = (pairs[i][0], pairs[j][0], pairs[k][0])
                dst = (pairs[i][1], pairs[j][1], pairs[k][1])
                if len(set(src)) < 3 or len(set(dst)) < 3:
                    continue
                M = mobius_from(src, dst)
                break
            if M:
                break
        if M:
            break
    if M is None:
        return None, "no fit"
    for (q1, q2) in pairs:                       # VERIFY on all points
        if act(M, q1) != q2:
            return None, ("mismatch", q1, q2, act(M, q1))
    return _norm(M), None


def cycle_type_on_B(M, Bl):
    """cycle type of the permutation M induces on the 8-point branch locus."""
    idx = {q: i for i, q in enumerate(Bl)}
    perm = [idx[act(M, q)] for q in Bl]
    seen, cyc = set(), []
    for i in range(len(Bl)):
        if i in seen:
            continue
        c, j = 0, i
        while j not in seen:
            seen.add(j)
            j = perm[j]
            c += 1
        cyc.append(c)
    return tuple(sorted(cyc))


# ---------------------------------------------------------------------- driver

def run(p, A, B, label, e_list, branch=True, kmax=3):
    K = GF(p)
    E = EllipticCurve(K, [A, B])
    n = E.order()
    f = PolynomialRing(K, 'x')([B, A, 0, 1])
    print("=" * 84)
    print("%s | p=%d  y^2=x^3+%dx+%d | n=%d (%s) | f irreducible: %s | rational 2-tors: %d"
          % (label, p, A, B, n, "ODD" if n % 2 else "EVEN", f.is_irreducible(),
             len(f.roots())))
    Gen = E.gens()[0]
    rows = []
    for e in e_list:
        Rpt = Integer(e)*Gen
        if Rpt.is_zero() or Rpt[1] == 0:
            print("  e=%-3d R = O or 2-torsion -- deg G < 7, skipped" % e)
            continue
        Kl = PolynomialRing(K, 'l')
        D, F = DF_polys(K(A), K(B), Rpt[0], Rpt[1], Kl)
        G = D*F
        if G.degree() != 7 or not G.is_squarefree():
            print("  e=%-3d deg G=%d squarefree=%s -- skipped" % (e, G.degree(), G.is_squarefree()))
            continue
        Gc = [ZZ(t) for t in G.coefficients(sparse=False)]
        chisum, S_rat, S_conj, nchk, nsp, nin = validate(p, A, B, Rpt)
        assert chisum == S_rat - S_conj, \
            "INSTRUMENT FAIL: %d != %d - %d" % (chisum, S_rat, S_conj)
        counts = {k: count_C(p, k, Gc) for k in range(1, kmax + 1)}
        c1, c2, c3 = char_poly_coeffs(p, counts)
        assert counts[1] == p + 1 + chisum
        ok = (c1 == 0 and c2 == 0)
        rows.append((e, c1, c2, c3, ok))
        print("  e=%-3d R=(%s,%s) | D,F ok @%d pts | sum chi2(G)=%-5d = S_rat(%d)-S_conj(%d)"
              " | split=%d inert=%d" % (e, Rpt[0], Rpt[1], nchk, chisum, S_rat, S_conj, nsp, nin))
        print("        #C(F_p)=%-7d (p+1=%d)   #C(F_p^2)=%-9d (p^2+1=%d)   #C(F_p^3)=%d"
              % (counts[1], p + 1, counts[2], p**2 + 1, counts[3]))
        print("        c1=%-5d c2=%-6d c3=%-7d | P1 (c1=0): %s | P2 (c2=0): %s | Ch=T^6-%dT^3+%d: %s"
              % (c1, c2, c3, c1 == 0, c2 == 0, c3, p**3, ok))

    if branch and rows:
        Rpt = Integer(e_list[0])*Gen
        Bl, Dr, Fr, found = branch_group(p, A, B, Rpt)
        if found is None:
            print("  BRANCH GROUP: G does not split over F_{p^3} (expected for even n) -- skipped")
            return rows
        rat = [x for x in found if x[3]]
        nonsq = [x for x in found if not x[2]]
        print("  BRANCH GROUP over F-bar (|B|=8, all 336 triples): order %d | F_p-rational: %d"
              " | multiplier nu NON-square: %d" % (len(found), len(rat), len(nonsq)))
        print("        (D-roots: %d, F-roots: %d, plus infinity)" % (len(Dr), len(Fr)))
        K3 = GF(p**3, 'w')
        f3 = PolynomialRing(K3, 'x')([B, A, 0, 1])
        tors = [r for r, _ in f3.roots()]
        print("  E[2]\\{O} x-coords: %d in F_{p^3}, of which F_p-rational: %d"
              % (len(tors), sum(1 for t in tors if t in GF(p))))
        sigs = []
        for tx in tors:
            M, err = sigma_T(p, A, B, Rpt, tx)
            if M is None:
                print("     sigma_T (Tx=%s): FIT/VERIFY FAILED %s" % (tx, err))
                continue
            inlist = any(M == Mf for (Mf, _, _, _) in found)
            ct = cycle_type_on_B(M, Bl)
            isrational = all(x in GF(p) for x in M)
            imginf = act(M, ('inf',))
            sigs.append(M)
            print("     sigma_T (Tx=%s): VERIFIED on all pts | in branch group: %s | cycle type"
                  " on B: %s | sigma(inf)=%s | F_p-rational: %s"
                  % (tx, inlist, ct, "inf" if imginf[0] == 'inf' else imginf[1], isrational))
        # do the three sigma_T + identity close up into a group?
        if len(sigs) == 3:
            prod12 = _norm(_mul(sigs[0], sigs[1]))
            print("     sigma_1 * sigma_2 == sigma_3 (in PGL2): %s" % (prod12 == sigs[2]))
            # Frobenius action: sigma_T^{(p)} should be sigma_{T^p}
            def frob(M):
                return _norm(tuple(x**p for x in M))
            perm = []
            for i, M in enumerate(sigs):
                Mf = frob(M)
                perm.append(next((j for j, N in enumerate(sigs) if N == Mf), None))
            print("     Frobenius permutation of (sigma_1,sigma_2,sigma_3): %s  -> 3-cycle: %s"
                  % (perm, sorted(perm) == [0, 1, 2] and len(set(perm)) == 3 and
                     all(perm[i] != i for i in range(3))))
    return rows


if __name__ == "__main__":
    allrows = []
    print("\n########## ARM 1: ODD n, j = 0 (the secp256k1 class) ##########")
    for (p, es) in [(43, [1, 2, 3, 5]), (67, [1, 2, 3]), (79, [1, 2])]:
        if EllipticCurve(GF(p), [0, 7]).order() % 2 == 1:
            allrows += run(p, 0, 7, "j=0 ODD-n", es)
    print("\n########## ARM 2: ODD n, generic j ##########")
    for (p, A, B, es) in [(79, 1, 6, [1, 2]), (61, 2, 1, [1, 2]), (103, 3, 5, [1, 2])]:
        E = EllipticCurve(GF(p), [A, B])
        if E.order() % 2 == 1:
            allrows += run(p, A, B, "generic-j ODD-n", es)
        else:
            print("(skip p=%d A=%d B=%d: n=%d even)" % (p, A, B, E.order()))
    print("\n########## ARM 3: CONTROL, EVEN n -- trace MUST be nonzero ##########")
    ctrl = []
    for (p, A, B, es) in [(43, 1, 0, [1, 2]), (43, 2, 3, [1, 2]), (67, 1, 5, [1, 2])]:
        E = EllipticCurve(GF(p), [A, B])
        if E.order() % 2 == 0:
            ctrl += run(p, A, B, "CONTROL even-n", es)

    print("\n" + "=" * 84)
    print("SUMMARY")
    print("  ODD-n cells: %d | P1&P2 hold (c1=c2=0): %d | violations: %d"
          % (len(allrows), sum(1 for r in allrows if r[4]), sum(1 for r in allrows if not r[4])))
    print("  EVEN-n control cells: %d | c1 != 0 (control FIRES): %d | c1 == 0 (control fails): %d"
          % (len(ctrl), sum(1 for r in ctrl if r[1] != 0), sum(1 for r in ctrl if r[1] == 0)))
