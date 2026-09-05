#!/usr/bin/env sage
"""jac26_e2_uniform_scale_v1.sage

End-to-end #26 conclusion, at scale.  The corpus verified  Sum_lambda chi2(G_R(lambda)) = 0
(equivalently c1 = 0, #C(F_p)=p+1, e2 = e1^2 - chi2(-1) p) only for p <= 211.  With closure now
proved a SYMBOLIC identity (jac26_closure_Vinvariance_v1.sage), the trace-0 argument is uniform;
this script confirms the theorem's own conclusion directly at large p = 7 mod 12, for several
random R != O, j=0 (secp class) and generic j.  Exact GF(p) arithmetic; chi2(0)=0.
"""
from sage.all import GF, EllipticCurve, ZZ, PolynomialRing, Integer


def chi2(v):
    if v == 0:
        return ZZ(0)
    return ZZ(1) if v.is_square() else ZZ(-1)


def DF(A, B, xR, yR, ring):
    l = ring.gen()
    return (l**4 - 6*xR*l**2 - 8*yR*l - (3*xR**2 + 4*A),
            yR*l**3 + (A + 3*xR**2)*l**2 + 3*xR*yR*l + yR**2)


def check(p, A, B, n_R=5):
    K = GF(p)
    E = EllipticCurve(K, [A, B])
    n = E.order()
    if n % 2 == 0:
        print("  [skip p=%d A=%d B=%d : n=%d even]" % (p, A, B, n))
        return
    Kl = PolynomialRing(K, 'l')
    worst = 0
    tested = 0
    for _ in range(n_R):
        R = E.random_point()
        if R.is_zero():
            continue
        xR, yR = R[0], R[1]
        D, F = DF(K(A), K(B), xR, yR, Kl)
        s = sum(chi2(D(l) * F(l)) for l in K)
        worst = max(worst, abs(Integer(s)))
        tested += 1
    print("  p=%-8d (p mod 12=%d)  A=%d B=%d  n=%-9d j=%-6s | %d random R:  max|Sum chi2(G_R)| = %d"
          % (p, p % 12, A, B, n, str(E.j_invariant()), tested, worst))


if __name__ == "__main__":
    print("=" * 84)
    print("END-TO-END #26 at scale:  Sum_lambda chi2(G_R(lambda)) == 0  for every R != O ?")
    print("=" * 84)
    print("j=0 (secp class), p = 7 mod 12:")
    for p in (100003, 1000003, 10000019):
        if p % 12 == 7:
            check(p, 0, 7)
    print("j=0, other p mod 12 with odd n (theorem says n odd suffices, not j=0):")
    for p in (1000033,):     # 1000033 mod 12 = 1
        check(p, 0, 7)
    print("generic j, odd n, large p:")
    for (p, A, B) in ((1000003, 5, 11), (1000003, 2, 3), (10000019, 7, 13)):
        check(p, A, B)
