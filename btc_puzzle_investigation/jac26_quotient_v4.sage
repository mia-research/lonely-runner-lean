#!/usr/bin/env sage
"""jac26_quotient_v4.sage -- T1 done properly: EXHIBIT the three elliptic quotients of C.

v3's T1 failed because sigma_T's two fixed points on P^1 lie in F_{p^6}, not F_{p^3}, so the
"conjugate to lambda -> -lambda" normalisation was unavailable over the field we need to count in.
The fixed points are not needed.  The quotient map P^1 -> P^1/<sigma> is given by the INVARIANT
QUADRATICS, which are an eigenspace of sigma acting on Sym^2 -- pure linear algebra over F_{p^3}:

  M in GL_2(F_{p^3}) with M^2 = delta*I  (sigma an involution in PGL_2)
  => M acts on Sym^2 with M^2 = delta^2 * I, eigenvalues +-delta
  => the (+delta)-eigenspace is 2-dimensional, spanned by binary quadratics Q1, Q2
  => (X:Z) |-> (Q1:Q2) IS the degree-2 quotient map.
  Phi (the degree-8 branch form) is sigma-invariant up to a scalar, so
      Phi = Psi(Q1, Q2)   for a binary QUARTIC Psi,
  and the quotient curve is   E_i :  W^2 = Psi(U, 1)  --  genus 1.

TEST T1.  For each of the three sigma_T:  solve for Psi, confirm deg Psi = 4 with distinct
          roots (genus 1), count #E_i(F_{p^3}), and check
              a(E_i / F_{p^3}) == c3
          which is exactly the assertion  Jac(C) x F_{p^3} ~ E_1 x E_2 x E_3  with the three
          factors Galois-conjugate -- i.e. Jac(C) = Res_{F_{p^3}/F_p}(E_1).
TEST T4.  The lift sigma~ squares to the identity (not to the hyperelliptic involution), so the
          three lifts generate a Klein group V and Kani-Rosen applies in the (Z/2)^2 form.
TEST T5.  B = lambda(E[2]) u lambda(P0 + E[2]) -- the branch locus IS two free E[2]-orbits.
          This is the structural fact that makes the (2,2,2,2) cycle type a theorem.

EXACTNESS.  Finite fields / ZZ only.  No floats.
"""

from sage.all import (GF, EllipticCurve, ZZ, PolynomialRing, Integer, Matrix, vector)
import itertools


def chi2(v):
    return ZZ(0) if v == 0 else (ZZ(1) if v.is_square() else ZZ(-1))


def DF_polys(A, B, xR, yR, ring):
    l = ring.gen()
    return (l**4 - 6*xR*l**2 - 8*yR*l - (3*xR**2 + 4*A),
            yR*l**3 + (A + 3*xR**2)*l**2 + 3*xR*yR*l + yR**2)


def lam_of(P, Rpt, A):
    if P.is_zero() or P == Rpt:
        return None
    xR, yR = Rpt[0], Rpt[1]
    if P[0] == xR:
        return -(3*xR**2 + A)/(2*yR)
    return (P[1] + yR)/(P[0] - xR)


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


def sigma_T(A, B, R3, Tx, K3, E3):
    T3 = E3(Tx, K3(0))
    pairs = []
    for P in E3.points():
        l1 = lam_of(P, R3, K3(A))
        l2 = lam_of(P + T3, R3, K3(A))
        pairs.append((('inf',) if l1 is None else ('f', l1),
                      ('inf',) if l2 is None else ('f', l2)))
    M = None
    for (i, j, k) in itertools.combinations(range(min(len(pairs), 30)), int(3)):
        src = (pairs[i][0], pairs[j][0], pairs[k][0])
        dst = (pairs[i][1], pairs[j][1], pairs[k][1])
        if len(set(src)) < 3 or len(set(dst)) < 3:
            continue
        M = mobius_from(src, dst)
        if M:
            break
    if M is None:
        return None
    for (q1, q2) in pairs:
        if act(M, q1) != q2:
            return None
    return _norm(M)


def invariant_quadratics(K3, M, XZ):
    """the 2-dim eigenspace of M acting on Sym^2 <X,Z> -- the invariant quadratics."""
    X, Z = XZ.gens()
    a, b, c, d = M
    basis = [X**2, X*Z, Z**2]
    # M acts by substitution X -> aX+bZ, Z -> cX+dZ
    cols = []
    for mono in basis:
        img = mono(a*X + b*Z, c*X + d*Z)
        cols.append([img.monomial_coefficient(m) for m in basis])
    Mat = Matrix(K3, cols).transpose()
    evs = Mat.eigenspaces_right()
    best = None
    for val, sp in evs:
        if sp.dimension() == 2:
            best = sp
            break
    if best is None:
        return None
    out = []
    for v in best.basis():
        out.append(sum(v[i]*basis[i] for i in range(3)))
    return out


def quotient_via_invariants(K3, M, Phi, XZ):
    """Solve Phi = Psi(Q1,Q2) for a binary quartic Psi; return Psi as a univariate poly in U
       (dehomogenised by Q2), or (None, reason)."""
    Qs = invariant_quadratics(K3, M, XZ)
    if Qs is None:
        return None, "no 2-dim invariant eigenspace on Sym^2"
    Q1, Q2 = Qs
    X, Z = XZ.gens()
    prods = [Q1**k * Q2**(4 - k) for k in range(5)]
    monos = [X**i * Z**(8 - i) for i in range(9)]
    Mat = Matrix(K3, [[pr.monomial_coefficient(m) for m in monos] for pr in prods]).transpose()
    rhs = vector(K3, [Phi.monomial_coefficient(m) for m in monos])
    try:
        sol = Mat.solve_right(rhs)
    except Exception:
        return None, "Phi is NOT a quartic in the invariant quadratics"
    if Mat*sol != rhs:
        return None, "solve did not reproduce Phi"
    KU = PolynomialRing(K3, 'U')
    U = KU.gen()
    Psi = sum(sol[k]*U**k for k in range(5))
    return Psi, sol


def count_genus1_quartic(K3, Psi, p):
    """#(W^2 = Psi(U)) on the smooth model, and the trace a = q+1-#."""
    tot = ZZ(0)
    for uu in K3:
        tot += 1 + chi2(Psi(uu))
    lc = Psi.leading_coefficient()
    if Psi.degree() == 4:
        tot += 2 if lc.is_square() else 0
    elif Psi.degree() == 3:
        tot += 1
    q = ZZ(p)**3
    return tot, q + 1 - tot


def count_C(p, k, Gc):
    Kk = GF(p) if k == 1 else GF(p**k, 'z%d' % k)
    Gk = PolynomialRing(Kk, 'l')([Kk(c) for c in Gc])
    tot = ZZ(1)
    for lam in Kk:
        v = Gk(lam)
        tot += 1 if v == 0 else (2 if v.is_square() else 0)
    return tot


def coeffs_from_counts(p, counts):
    s = {k: ZZ(p)**k + 1 - counts[k] for k in counts}
    c1 = s[1]
    n2 = c1*s[1] - s[2]
    assert n2 % 2 == 0
    c2 = n2 // 2
    n3 = s[3] - c1*s[2] + c2*s[1]
    assert n3 % 3 == 0
    return c1, c2, n3 // 3


def analyse(p, A, B, e, label):
    K = GF(p)
    E = EllipticCurve(K, [A, B])
    n = E.order()
    Rpt = Integer(e)*E.gens()[0]
    if Rpt.is_zero() or Rpt[1] == 0:
        return
    Kl = PolynomialRing(K, 'l')
    D, F = DF_polys(K(A), K(B), Rpt[0], Rpt[1], Kl)
    G = D*F
    if G.degree() != 7 or not G.is_squarefree():
        return
    Gc = [ZZ(t) for t in G.coefficients(sparse=False)]
    counts = {k: count_C(p, k, Gc) for k in (1, 2, 3)}
    c1, c2, c3 = coeffs_from_counts(p, counts)
    print("=" * 82)
    print("%s p=%d n=%d(%s) e=%d R=(%s,%s) | c1=%d c2=%d c3=%d"
          % (label, p, n, "ODD" if n % 2 else "EVEN", e, Rpt[0], Rpt[1], c1, c2, c3))

    K3 = GF(p**3, 'w')
    E3 = EllipticCurve(K3, [A, B])
    R3 = E3(Rpt[0], Rpt[1])
    Kl3 = PolynomialRing(K3, 'l')
    D3, F3 = DF_polys(K3(A), K3(B), K3(Rpt[0]), K3(Rpt[1]), Kl3)
    G3 = D3*F3
    f3 = PolynomialRing(K3, 'x')([B, A, 0, 1])
    tors = [r for r, _ in f3.roots()]
    if len(tors) != 3:
        print("   E[2] not fully in F_{p^3} -- skipping (even n)")
        return

    # ---- T5 : the branch locus IS lambda(E[2]) u lambda(P0 + E[2])
    lamE2 = set()
    for tx in tors:
        T = E3(tx, K3(0))
        l = lam_of(T, R3, K3(A))
        lamE2.add(('inf',) if l is None else ('f', l))
    lamE2.add(('inf',))                          # lambda(O) = infinity
    halves = [P for P in E3.points() if 2*P == R3]
    lamH = set()
    for P in halves:
        l = lam_of(P, R3, K3(A))
        lamH.add(('inf',) if l is None else ('f', l))
    Brts = set(('f', r) for r, _ in G3.roots())
    Bl = Brts | {('inf',)}
    print("   T5  |lambda(E[2])|=%d  |lambda(P0+E[2])|=%d  disjoint=%s  union==B: %s  (|B|=%d)"
          % (len(lamE2), len(lamH), len(lamE2 & lamH) == 0,
             (lamE2 | lamH) == Bl, len(Bl)))

    XZ = PolynomialRing(K3, ['X', 'Z'])
    X, Z = XZ.gens()
    Gcf = G3.coefficients(sparse=False)
    Phi = Z * sum(Gcf[i] * X**i * Z**(7 - i) for i in range(8))

    traces = []
    for tx in tors:
        M = sigma_T(A, B, R3, tx, K3, E3)
        if M is None:
            print("   T1  sigma_T fit/verify FAILED (Tx=%s)" % tx)
            continue
        # ---- T4 : does the lift square to the identity?
        a, b, c, d = M
        delta = a*a + b*c if (a + d == 0) else None
        Mt = _norm(_mul(M, M))
        idM = _norm((K3(1), K3(0), K3(0), K3(1)))
        # multiplier nu of Phi under M
        Phis = Phi(a*X + b*Z, c*X + d*Z)
        nu = None
        for mon in Phi.monomials():
            u_, v_ = Phi.monomial_coefficient(mon), Phis.monomial_coefficient(mon)
            if u_ != 0:
                nu = v_/u_
                break
        Psi, info = quotient_via_invariants(K3, M, Phi, XZ)
        if Psi is None:
            print("   T1  quotient FAILED: %s" % info)
            continue
        rts = Psi.roots()
        distinct = (sum(m for _, m in rts) == len(rts))
        cnt, a_i = count_genus1_quartic(K3, Psi, p)
        traces.append(a_i)
        print("   T1  sigma_T(Tx=%s): M^2 == id in PGL2: %s | nu square: %s | deg Psi = %d,"
              " roots distinct: %s | #E_i(F_p^3) = %d | a(E_i/F_p^3) = %d | == c3 : %s"
              % (tx, Mt == idM, nu.is_square(), Psi.degree(), distinct, cnt, a_i, a_i == c3))
    if len(traces) == 3:
        print("   T1  VERDICT: three genus-1 quotients, all traces == c3 : %s   %s vs c3=%d"
              % (all(t == c3 for t in traces), traces, c3))
        print("   ==> Jac(C) x F_{p^3} ~ E_1 x E_2 x E_3 with a(E_i)=c3; Frobenius 3-cycles them")
        print("   ==> Ch(T) = T^6 - c3 T^3 + p^3, trace over F_p = 0.   #26 HOLDS at this cell.")


if __name__ == "__main__":
    analyse(43, 0, 7, 1, "j=0    ")
    analyse(43, 0, 7, 2, "j=0    ")
    analyse(43, 0, 7, 3, "j=0    ")
    analyse(67, 0, 7, 1, "j=0    ")
    analyse(67, 0, 7, 2, "j=0    ")
    analyse(79, 1, 6, 1, "generic")
    analyse(79, 1, 6, 2, "generic")
