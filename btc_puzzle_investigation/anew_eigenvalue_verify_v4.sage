#!/usr/bin/env sage
# VALIDATE the abelian-discriminator before trusting the p=13/p=43 split.
# Galois-necessary test: sigma(D)/D in (K^*)^2 for all sigma in Gal(K/Q).  If it FAILS, K(sqrt D)/Q
# is not even Galois => definitively NON-abelian.  Validate on plants, then detail p=13 vs p=43.
import sys
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core

def galois_test(D, K, z, m, verbose=False):
    gens = [Integer(g) for g in Zmod(m).unit_gens()]
    for t in gens:
        r = (K.hom([z**t])(D)/D)
        sq = r.is_square()
        if verbose: print(f"    sigma_{t}(D)/D is_square = {sq}")
        if not sq:
            return False, t
    return True, None

def build_L(p, a, K, z, n):
    dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
    V1 = sum(h1[d]*z**((a*d) % n) for d in range(n))
    V2 = sum(h2[d]*z**((a*d) % n) for d in range(n))
    leg = 1 if p % 4 == 1 else -1
    e1 = -V1; e2 = (V1**2 + V2)/2; e3 = leg*p*e1; e4 = K(p**2)
    R = PolynomialRing(K, 'T'); T = R.gen()
    return T**4 - e1*T**3 + e2*T**2 - e3*T + e4

def run(p, a=1):
    n = core.curve_order(p); m = 12*n
    K = CyclotomicField(m); z = K.gen()
    Kn = CyclotomicField(n); zn = Kn.gen()
    L = build_L(p, a, Kn, zn, n)
    phi = Kn.hom([z**12], K)
    R = PolynomialRing(K, 'T'); T = R.gen()
    Lb = sum(phi(c)*T**i for i, c in enumerate(L.list()))
    facs = [f for f, e in Lb.factor()]
    degs = sorted(f.degree() for f in facs)
    print(f"p={p} n={n} a={a}: factor degs over Q(zeta_{m}) = {degs}")
    if degs != [2, 2]:
        return
    # PLANTS validated in the SAME field K:
    okabel, _ = galois_test(K(5), K, z, m)
    oknon, _  = galois_test(z + 2, K, z, m)
    print(f"    [plant D=5   -> galois={okabel} (want True)]   [plant D=zeta+2 -> galois={oknon} (want False)]")
    for i, q in enumerate(facs):
        D = q[1]**2 - 4*q[0]
        if D.is_square():
            print(f"    quad {i}: D is a square -> splits (eigenvalues in Q(zeta_{m}))"); continue
        gal, t = galois_test(D, K, z, m)
        print(f"    quad {i}: Galois(sigma(D)/D in K^2 all sigma) = {gal}" + ("" if gal else f"  (FAILS at sigma_{t})")
              + ("  -> could be abelian" if gal else "  -> NON-ABELIAN (not even Galois/Q)"))

if __name__ == "__main__":
    run(13, 1)
    run(43, 1)
    run(67, 1)
