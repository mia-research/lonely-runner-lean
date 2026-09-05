#!/usr/bin/env sage
# FORK (1) decisive: is the splitting field of L*(a) ABELIAN over Q?
#   abelian  <=> contained in some Q(zeta_M) (Kronecker-Weber) <=> eigenvalues are cyclotomic
#            <=> Hecke-character / Jacobi-sum type  => L-Stick premise HOLDS.
#   non-abelian => eigenvalues are NOT Jacobi sums => L-Stick FAILS, go to L-mono.
# Also report the [2,2]-over-Q(zeta_12n) quadratic factors' discriminants: the splitting field
# is Q(zeta_12n)(sqrt(disc)); abelian iff sqrt(disc) generates an abelian extension.
import sys
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core

def build_L_over(p, a, K, z, n):
    dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
    V1 = sum(h1[d]*z**((a*d) % n) for d in range(n))
    V2 = sum(h2[d]*z**((a*d) % n) for d in range(n))
    leg = 1 if p % 4 == 1 else -1
    e1 = -V1; e2 = (V1**2 + V2)/2; e3 = leg*p*e1; e4 = K(p**2)
    R = PolynomialRing(K, 'T'); T = R.gen()
    return T**4 - e1*T**3 + e2*T**2 - e3*T + e4

def identify(p, a=1):
    n = core.curve_order(p); assert is_prime(n)
    # work over Q(zeta_12n) where L* = q1*q2 (from v1); test if sqrt(disc(qi)) is abelian over Q
    m = 12*n
    Kbig = CyclotomicField(m); zb = Kbig.gen()
    Kn = CyclotomicField(n); zn = Kn.gen()
    L = build_L_over(p, a, Kn, zn, n)
    phi = Kn.hom([zb**12], Kbig)
    Rb = PolynomialRing(Kbig, 'T'); Tb = Rb.gen()
    Lb = sum(phi(c)*Tb**i for i, c in enumerate(L.list()))
    fac = [f for f, e in Lb.factor()]
    degs = sorted(f.degree() for f in fac)
    out = f"p={p} n={n} a={a}: /Q(zeta_{m}) degs={degs}"
    if degs == [2, 2]:
        # each quadratic T^2 - s T + q has discriminant s^2 - 4q in Q(zeta_12n).
        # splitting field = Q(zeta_12n)(sqrt(D1), sqrt(D2)); abelian/Q iff each sqrt(Di) is.
        # test abelian by: is Di a square in Q(zeta_12n)?  (then already split, abelian)
        #   else does Q(zeta_12n)(sqrt Di) embed in a cyclotomic field?  Use is_abelian on the
        #   relative quadratic's absolute model.
        verdicts = []
        for q in fac:
            s = -q[1]; c0 = q[0]
            D = s*s - 4*c0
            if D.is_square():
                verdicts.append("split")
            else:
                # absolute field Q(zeta_12n)(sqrt D)
                Rq = PolynomialRing(Kbig, 'X'); X = Rq.gen()
                M = (X**2 - D).splitting_field('t')   # absolute number field
                ab = M.is_abelian() if hasattr(M, "is_abelian") else (M.is_galois() and M.galois_group().is_abelian())
                verdicts.append("ABELIAN" if ab else "non-abelian")
        out += f"  quad-ext verdicts = {verdicts}"
    print(out)

if __name__ == "__main__":
    identify(13, 1)
    identify(13, 2)
    identify(43, 1)
