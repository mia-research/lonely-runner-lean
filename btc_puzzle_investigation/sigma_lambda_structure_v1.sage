#!/usr/bin/env sage
# What does the omega-descent / sigma_lambda ACTUALLY force?  Evidence, not verdict.
# For each p: build L*(a) exactly over K=Q(zeta_n) from the exact histograms, then report
#   (1) descent: sigma_lambda(L*) == L*  [confirms L* over the index-3 subfield]
#   (2) factorization type of L* over Q(zeta_n)  [pins how sigma_lambda can permute roots]
#   (3) order of the ratio u = alpha2/alpha1  [we proved =3; recheck]
#   (4) is L* irreducible over the index-3 subfield F0 = fixed field of sigma_lambda?
# so we can state precisely what the descent constrains vs. leaves free.
import sys
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core

def cube_root_mod(n):
    F = GF(n); g = F.multiplicative_generator()
    lam = Integer(g**((n-1)//3))
    assert lam != 1 and pow(lam,3,n) == 1
    return lam

def analyze(p, a=1):
    n = core.curve_order(p); assert is_prime(n)
    dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
    lam = cube_root_mod(n)
    K.<z> = CyclotomicField(n)
    V1 = sum(h1[d]*z**((a*d) % n) for d in range(n))
    V2 = sum(h2[d]*z**((a*d) % n) for d in range(n))
    leg = 1 if p % 4 == 1 else -1
    e1 = -V1; e2 = (V1**2 + V2)/2; e3 = leg*p*e1; e4 = K(p**2)
    R.<T> = K[]
    L = T**4 - e1*T**3 + e2*T**2 - e3*T + e4
    # (1) descent
    sig = K.hom([z**lam])
    Lsig = R([sig(c) for c in L.list()])
    descent = (Lsig == L)
    # (2) factorization over K
    fac = L.factor()
    degs = sorted([f.degree() for f, m in fac for _ in range(m)])
    # (3) order of u = alpha2/alpha1 via a complex embedding
    emb = K.complex_embedding(prec=200)
    Rc.<Tc> = CC[]
    Lc = Rc([emb(c) for c in L.list()])
    rts = [r for r, m in Lc.roots(CC)]
    def order_of(x, cap=60):
        for k in range(1, cap+1):
            if abs(x**k - 1) < 1e-30:
                return k
        return None
    # all pairwise ratios and their (root-of-unity) orders
    ords = set()
    for i in range(4):
        for j in range(4):
            if i != j:
                o = order_of(rts[i]/rts[j])
                if o: ords.add(o)
    # (4) irreducible over the fixed field F0 of sigma_lambda?  Test: does L factor over K
    #     into sigma-orbits?  If L is irreducible/degree-4 over K and descends, its coeffs are
    #     in F0; check whether L is irreducible over K (a necessary probe).
    irr_over_K = (len(degs) == 1 and degs[0] == 4)
    print(f"p={p:>4} n={n:>4} lam={lam:>4} a={a}: descent(sigma_L==L)={descent} | "
          f"factor degs /K = {degs} | pairwise-ratio orders = {sorted(ords)} | irred/K={irr_over_K}")
    return descent, degs, sorted(ords)

for p in (43, 67, 127):
    analyze(p, a=1)
    analyze(p, a=2)
