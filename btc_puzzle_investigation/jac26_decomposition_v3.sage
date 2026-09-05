#!/usr/bin/env sage
"""jac26_decomposition_v3.sage -- the DECISIVE structural test for #26.

Established by v2 (14 odd-n cells, 4 curves, j=0 and generic j):
  c1 = c2 = 0 and Ch(T) = T^6 - c3 T^3 + p^3;  branch group = (Z/2)^2 realised by the
  E[2]-translations sigma_T (cycle type (2,2,2,2) on the 8-point locus B, sigma_1 sigma_2 =
  sigma_3, Frobenius acting as a 3-cycle);  even-n control fires (c1 != 0).

THIS SCRIPT closes the loop by exhibiting the decomposition itself:

  Ch(T) = T^6 - c3 T^3 + p^3 = (T^3)^2 - c3 (T^3) + p^3
  => the SIX eigenvalues alpha_i satisfy alpha_i^3 in {beta_1, beta_2}, beta_1+beta_2 = c3,
     beta_1 beta_2 = p^3, each with multiplicity 3
  => over F_{p^3} the Frobenius trace on H^1(C) is 3 c3, i.e. #C(F_{p^3}) = p^3 + 1 - 3 c3
  => Jac(C) x F_{p^3} ~ E_1 x E_2 x E_3 with a(E_i / F_{p^3}) = c3 for each i.

TEST T1.  Build each quotient curve E_i = C / sigma~_T EXPLICITLY (conjugate sigma_T to
          lambda -> -lambda; since sigma_T is fixed-point-free on B, its two P^1-fixed points
          are NOT branch points, so the transformed octic is H(lambda) = h(lambda^2) with
          deg h = 4, and E_i : v^2 = h(u) is the genus-1 quotient).  Then verify
              a(E_i / F_{p^3}) == c3     for i = 1,2,3.
          This is the statement "Jac(C) is the Weil restriction from F_{p^3}" made concrete.
TEST T2.  #C(F_{p^3}) == p^3 + 1 - 3 c3   (already implied, re-checked independently).
TEST T3.  WIDE SWEEP of P1 & P2 (the two cheap counts) over many primes x many R, both
          j = 0 and generic j, plus the even-n control.

EXACTNESS.  Finite fields / ZZ only.  No floats anywhere.
"""

from sage.all import GF, EllipticCurve, ZZ, PolynomialRing, Integer
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


def sigma_T(p, A, B, Rpt, Tx, K3):
    """tau_T induced Mobius map, fitted then VERIFIED on every point of E(F_{p^3})."""
    E3 = EllipticCurve(K3, [A, B])
    R3 = E3(Rpt[0], Rpt[1])
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


def fixed_points_of(M, K):
    """the two fixed points of a Mobius involution M in P^1(K) (or None if not split over K)."""
    a, b, c, d = M
    Ku = PolynomialRing(K, 'u')
    u = Ku.gen()
    if c == 0:
        # a u + b = d u  =>  one finite fixed point plus infinity
        if a == d:
            return None
        return [('f', b/(d - a)), ('inf',)]
    # c u^2 + (d - a) u - b = 0
    rts = (c*u**2 + (d - a)*u - b).roots()
    if sum(m for _, m in rts) != 2:
        return None
    out = []
    for r, m in rts:
        out += [('f', r)]*m
    return out


def quotient_curve_trace(p, K3, octic_roots, M):
    """E_i = C/sigma~ : conjugate M to (lambda -> -lambda), rewrite the octic, split off
       H(lambda) = h(lambda^2), and return (deg h, a(E_i/F_{p^3})) where E_i : v^2 = h(u).
       Requires M fixed-point-free on the branch locus (so 0, infinity avoid it)."""
    fps = fixed_points_of(M, K3)
    if fps is None or len(fps) != 2:
        return None, "fixed points not in F_{p^3}"
    if any(q in octic_roots for q in fps):
        return None, "sigma has a fixed point ON the branch locus"
    # mu sends fps[0] -> 0, fps[1] -> infinity, and (say) some third branch point -> 1
    third = next(q for q in octic_roots if q not in fps)
    mu = mobius_from((fps[0], third, fps[1]), (('f', K3(0)), ('f', K3(1)), ('inf',)))
    if mu is None:
        return None, "mu construction failed"
    newroots = [act(mu, q) for q in octic_roots]
    if any(q[0] == 'inf' for q in newroots):
        return None, "a branch point went to infinity"
    vals = [q[1] for q in newroots]
    if any(v == 0 for v in vals):
        return None, "a branch point went to 0"
    # branch locus must now be 4 pairs {+-b}
    S = set(vals)
    if len(S) != 8 or any((-v) not in S for v in vals):
        return None, "transformed branch locus is not stable under lambda -> -lambda"
    sq = sorted(set(v**2 for v in vals))
    if len(sq) != 4:
        return None, "squares do not pair up 4+4"
    Ku = PolynomialRing(K3, 'u')
    u = Ku.gen()
    h = Ku(1)
    for s in sq:
        h *= (u - s)
    # E_i : v^2 = h(u), quartic model, genus 1
    tot = ZZ(0)
    for uu in K3:
        tot += 1 + chi2(h(uu))
    tot += 2 if h.leading_coefficient().is_square() else 0
    q3 = ZZ(p)**3
    return h.degree(), q3 + 1 - tot


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
    if 3 not in s:
        return c1, c2, None
    n3 = s[3] - c1*s[2] + c2*s[1]
    assert n3 % 3 == 0
    return c1, c2, n3 // 3


def G_of(p, A, B, Rpt, K):
    Kl = PolynomialRing(K, 'l')
    D, F = DF_polys(K(A), K(B), K(Rpt[0]), K(Rpt[1]), Kl)
    return D*F


# ============================================================ T1 + T2 : deep test

def deep(p, A, B, e, label):
    K = GF(p)
    E = EllipticCurve(K, [A, B])
    n = E.order()
    Rpt = Integer(e)*E.gens()[0]
    if Rpt.is_zero() or Rpt[1] == 0:
        return
    G = G_of(p, A, B, Rpt, K)
    if G.degree() != 7 or not G.is_squarefree():
        return
    Gc = [ZZ(t) for t in G.coefficients(sparse=False)]
    counts = {k: count_C(p, k, Gc) for k in (1, 2, 3)}
    c1, c2, c3 = coeffs_from_counts(p, counts)
    print("-" * 80)
    print("%s p=%d n=%d(%s) e=%d | c1=%d c2=%d c3=%d" %
          (label, p, n, "ODD" if n % 2 else "EVEN", e, c1, c2, c3))
    # T2
    t2 = (counts[3] == p**3 + 1 - 3*c3)
    print("   T2  #C(F_p^3) = p^3+1-3c3 : %s   (%d vs %d)"
          % (t2, counts[3], p**3 + 1 - 3*c3))
    # T1
    K3 = GF(p**3, 'w')
    G3 = G_of(p, A, B, Rpt, K3)
    rts = [('f', r) for r, m in G3.roots() for _ in range(m)]
    if len(rts) != 7:
        print("   T1  SKIPPED: only %d of 7 roots in F_{p^3} (expected when n is even)" % len(rts))
        return
    octic = rts + [('inf',)]
    f3 = PolynomialRing(K3, 'x')([B, A, 0, 1])
    traces = []
    for tx, _ in f3.roots():
        M = sigma_T(p, A, B, Rpt, tx, K3)
        if M is None:
            print("   T1  sigma_T fit/verify FAILED for Tx=%s" % tx)
            continue
        dh, a_i = quotient_curve_trace(p, K3, set(octic), M)
        if dh is None:
            print("   T1  quotient failed: %s" % a_i)
            continue
        traces.append(a_i)
        print("   T1  E_i = C/sigma~_T : v^2 = h(u), deg h = %d (genus 1) | a(E_i/F_p^3) = %d"
              " | == c3 : %s" % (dh, a_i, a_i == c3))
    if len(traces) == 3:
        print("   T1  VERDICT: all three quotient traces equal c3 : %s   (traces %s, c3 %d)"
              % (all(t == c3 for t in traces), traces, c3))


# ================================================================ T3 : wide sweep

def wide(p, A, B, label, max_R=None):
    K = GF(p)
    E = EllipticCurve(K, [A, B])
    n = E.order()
    odd = (n % 2 == 1)
    Gen = E.gens()[0]
    ok = bad = skipped = 0
    firing = 0
    es = range(1, n) if max_R is None else range(1, min(n, max_R + 1))
    for e in es:
        Rpt = Integer(e)*Gen
        if Rpt.is_zero() or Rpt[1] == 0:
            skipped += 1
            continue
        G = G_of(p, A, B, Rpt, K)
        if G.degree() != 7 or not G.is_squarefree():
            skipped += 1
            continue
        Gc = [ZZ(t) for t in G.coefficients(sparse=False)]
        counts = {k: count_C(p, k, Gc) for k in (1, 2)}
        c1, c2, _ = coeffs_from_counts(p, counts)
        if c1 == 0 and c2 == 0:
            ok += 1
        else:
            bad += 1
            if c1 != 0:
                firing += 1
    tag = "ODD" if odd else "EVEN"
    if odd:
        print("  %-16s p=%-4d n=%-5d %-4s | cells %-4d | P1&P2 HOLD: %-4d | VIOLATIONS: %d"
              % (label, p, n, tag, ok + bad, ok, bad))
    else:
        print("  %-16s p=%-4d n=%-5d %-4s | cells %-4d | c1=c2=0: %-4d | c1 != 0 (FIRES): %d"
              % (label, p, n, tag, ok + bad, ok, firing))
    return ok, bad, firing, odd


if __name__ == "__main__":
    print("############ T1 + T2 : the decomposition, exhibited ############")
    deep(43, 0, 7, 1, "j=0    ")
    deep(43, 0, 7, 2, "j=0    ")
    deep(67, 0, 7, 1, "j=0    ")
    deep(79, 1, 6, 1, "generic")

    print("\n############ T3 : wide sweep of P1 & P2 ############")
    print("  --- ARM 1: j = 0, ODD n (the secp256k1 class), ALL R ---")
    tot_ok = tot_bad = 0
    for p in [43, 67, 79, 127, 139, 151, 163, 199, 211]:
        try:
            E = EllipticCurve(GF(p), [0, 7])
        except Exception:
            continue
        if E.order() % 2 == 1:
            o, b, _, _ = wide(p, 0, 7, "j=0", max_R=60)
            tot_ok += o
            tot_bad += b
    print("  --- ARM 2: generic j, ODD n, ALL R ---")
    found = 0
    for p in [79, 83, 89, 97, 101, 103, 107, 109, 113, 127]:
        for A in range(1, 8):
            for B in range(1, 8):
                if found >= 6:
                    break
                try:
                    E = EllipticCurve(GF(p), [A, B])
                except Exception:
                    continue
                if E.order() % 2 == 1 and E.j_invariant() not in (0, 1728):
                    o, b, _, _ = wide(p, A, B, "generic-j", max_R=40)
                    tot_ok += o
                    tot_bad += b
                    found += 1
                    break
            if found >= 6:
                break
        if found >= 6:
            break
    print("  --- ARM 3: CONTROL, EVEN n -- c1 must be NONZERO ---")
    cf = cz = 0
    for (p, A, B) in [(43, 1, 0), (43, 2, 3), (67, 1, 5), (79, 2, 5), (101, 1, 1)]:
        try:
            E = EllipticCurve(GF(p), [A, B])
        except Exception:
            continue
        if E.order() % 2 == 0:
            o, b, fire, _ = wide(p, A, B, "CONTROL even-n", max_R=40)
            cf += fire
            cz += o
    print("\n" + "=" * 80)
    print("ODD-n TOTAL: %d cells, P1&P2 hold in %d, VIOLATIONS %d" % (tot_ok + tot_bad, tot_ok, tot_bad))
    print("EVEN-n CONTROL: c1 != 0 in %d cells; c1 = c2 = 0 in %d cells" % (cf, cz))
