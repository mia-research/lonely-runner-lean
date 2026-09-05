#!/usr/bin/env sage
# FORK (1): what ARE the a != 0 twisted eigenvalues?
# Decisive test: does L*(a) split COMPLETELY over Q(zeta_{12n})?
#   YES -> eigenvalues are cyclotomic integers in Q(zeta_{12n}) = abelian over Q
#          => Hecke-character / Jacobi-sum type => Stickelberger governs them (L-Stick premise HOLDS).
#   NO  -> splitting field is non-abelian => NOT Jacobi sums => L-Stick premise FAILS, go to L-mono.
# Exact number-field arithmetic (no float in the decision).
import sys
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core

def build_L(p, a, K, z):
    n = K._n() if hasattr(K, "_n") else K.zeta_order()
    dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
    V1 = sum(h1[d]*z**((a*d) % n) for d in range(n))
    V2 = sum(h2[d]*z**((a*d) % n) for d in range(n))
    leg = 1 if p % 4 == 1 else -1
    e1 = -V1; e2 = (V1**2 + V2)/2; e3 = leg*p*e1; e4 = K(p**2)
    R = PolynomialRing(K, 'T'); T = R.gen()
    return T**4 - e1*T**3 + e2*T**2 - e3*T + e4

def identify(p, a=1):
    n = core.curve_order(p); assert is_prime(n)
    K = CyclotomicField(n); z = K.gen()
    L = build_L(p, a, K, z)
    # move to Kbig = Q(zeta_{12n}); zeta_n = zeta_{12n}^12
    m = 12*n
    Kbig = CyclotomicField(m); zb = Kbig.gen()
    phi = K.hom([zb**12], Kbig)
    Rbig = PolynomialRing(Kbig, 'T'); Tb = Rbig.gen()
    Lbig = sum(phi(c)*Tb**i for i, c in enumerate(L.list()))
    fac = Lbig.factor()
    degs = sorted([f.degree() for f, e in fac for _ in range(e)])
    splits = all(d == 1 for d in degs)
    print(f"p={p:>4} n={n:>4} a={a}: over Q(zeta_{m}) [deg {Kbig.degree()}]  factor degs = {degs}  "
          f"-> {'SPLITS (cyclotomic eigenvalues!)' if splits else 'does NOT fully split'}")
    return splits, degs

if __name__ == "__main__":
    for p in (13, 43):
        for a in (1, 2):
            identify(p, a)
