#!/usr/bin/env sage
# lmono_brick2_tensor_shadow_v1.sage — L-mono brick 2 (PLAN_lmono_monodromy_campaign_v1.md §7.2):
# the TENSOR-STRUCTURE SHADOW test. At fresh cells, verify EXACTLY that the [2,2] factorization of
# L*(a) over K = Q(zeta_{12n}) has its two quadratics related by the zeta_3-RESCALING:
#     roots(g2) = zeta_3 * roots(g1)   <=>   g2 = T^2 - rho*s1*T + rho^2*u1   (g1 = T^2 - s1*T + u1)
# for some ordering and rho in {zeta_3, zbar_3}. This is T2 (the cross-plane trace identity
# Tr(pi|W') = zeta_3 Tr(pi|W)) verified at the FACTOR level — stronger than the numeric multiset
# certificate of RESULT_d2_twist_rigidity_certificate_v1, cheaper than the [2,2]-deg certificates.
import sys, time
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core

def build_L(p, a, Kn, zn, n):
    dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
    V1 = sum(h1[d]*zn**((a*d) % n) for d in range(n))
    V2 = sum(h2[d]*zn**((a*d) % n) for d in range(n))
    leg = 1 if p % 4 == 1 else -1
    e1 = -V1; e2 = (V1**2 + V2)/2; e3 = leg*p*e1; e4 = Kn(p**2)
    R = PolynomialRing(Kn, 'T'); T = R.gen()
    return T**4 - e1*T**3 + e2*T**2 - e3*T + e4

def run(p, a):
    t0 = time.time()
    n = core.curve_order(p); m = 12*n
    K = CyclotomicField(m); z = K.gen()
    Kn = CyclotomicField(n); zn = Kn.gen()
    L = build_L(p, a, Kn, zn, n)
    phi = Kn.hom([z**12], K)
    R = PolynomialRing(K, 'T'); T = R.gen()
    Lb = sum(phi(c)*T**i for i, c in enumerate(L.list()))
    facs = [f for f, e in Lb.factor()]
    degs = sorted(f.degree() for f in facs)
    if degs != [2, 2]:
        print(f"p={p} a={a}: factor degs {degs} != [2,2] — cannot test (report)", flush=True)
        return None
    z3a = z**(4*n)                     # zeta_3 = zeta_{12n}^{4n}
    assert z3a**3 == 1 and z3a != 1
    z3b = z3a**2
    g1, g2 = facs
    s1 = -g1[1]; u1 = g1[0]            # g1 = T^2 - s1 T + u1 (monic)
    hit = []
    for rho in (z3a, z3b):
        pred = T**2 - rho*s1*T + rho**2*u1
        if pred == g2:
            hit.append("direct")
        pred2 = T**2 - rho**2*s1*T + rho*u1
        if pred2 == g2:
            hit.append("conjugate-rescale")
    # also the swapped ordering (g2 as base)
    s2 = -g2[1]; u2 = g2[0]
    for rho in (z3a, z3b):
        if T**2 - rho*s2*T + rho**2*u2 == g1:
            hit.append("swapped")
    print(f"p={p:>4} n={n:>4} a={a}: zeta3-RESCALING of the [2,2] factors: "
          f"{'EXACT (' + ','.join(hit) + ')' if hit else 'NOT FOUND'}  [{time.time()-t0:.0f}s]", flush=True)
    return bool(hit)

if __name__ == "__main__":
    ok = 0; tot = 0
    for (p, a) in [(79,1), (127,1), (163,1), (61,1), (211,1), (61,2), (79,2)]:
        r = run(p, a)
        if r is not None:
            tot += 1; ok += bool(r)
    print(f"\nTENSOR-STRUCTURE SHADOW (T2 at factor level): {ok}/{tot} fresh cells EXACT", flush=True)
