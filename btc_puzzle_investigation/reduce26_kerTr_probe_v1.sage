#!/usr/bin/env sage
"""reduce26_kerTr_probe_v1.sage -- the coset/character lead for #26's inert sum.

KEY FACT: Tr: E(F_{p^2}) -> E(F_p), Tr(P)=P+phi(P), is a group hom. ker(Tr) = {P : phi(P) = -P},
i.e. x in F_p, y^p = -y -- these are E'(F_p) (the quadratic twist), order #E' = 2p+2 - #E.
The inert fibre Tr^{-1}(R) is a COSET of ker(Tr). So
  Sum_conj(R) = sum over P in (coset of ker Tr, minus rational points) of chi_2(N(y_P))
is a CHARACTER SUM OVER A COSET of the twist group.

This script: (1) confirm #ker(Tr) = #E'(F_p); (2) build the coset for a given R; (3) test whether
chi_2(N(y_P)) is a multiplicative character of the coset (i.e. chi_2(N(y_{P+K})) / chi_2(N(y_P)) is
independent of P for K in ker(Tr)); (4) if it's a nontrivial character, the coset-sum is a Gauss sum.
"""
from sage.all import GF, EllipticCurve, ZZ


def chi2(a, p):
    a = int(a) % p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1


if __name__ == "__main__":
    p, A, B = 43, 0, 7
    Fp = GF(p); Fp2 = GF(p**2, 'a')
    E = EllipticCurve(Fp, [A, B]); n = E.order()
    E2 = E.change_ring(Fp2)
    # the quadratic twist E'
    Eprime = E.quadratic_twist()
    EprimeFp = Eprime.change_ring(Fp) if Eprime.base_ring() != Fp else Eprime
    nprime = EprimeFp.order()
    print("p=%d E:y^2=x^3+%d : #E(F_p)=%d  #E'(F_p)=%d  (2p+2-%d=%d)"%(p,B,n,nprime,n,2*p+2-n))

    # ker(Tr): points P in E(F_{p^2}) with phi(P) = -P, i.e. P + phi(P) = O.
    kerTr = []
    for x1 in Fp2:
        rhs = x1**3 + A*x1 + B
        if not rhs.is_square(): continue
        y1 = rhs.sqrt()
        for sg in (1,-1):
            P = E2(x1, sg*y1)
            if P.is_zero(): continue
            phiP = E2(P[0]**p, P[1]**p)
            if phiP == -P:
                kerTr.append(P)
    print("#ker(Tr) = %d  (expect #E' = %d): %s"%(len(kerTr), nprime, len(kerTr)==nprime))

    # pick R, build the inert coset Tr^{-1}(R) minus rational points
    G = next(P for P in E if P.order()==n)
    for e in (1,3,5):
        R = e*G; R2 = E2(R[0],R[1])
        # inert points with Tr(P)=R: P + phi(P) = R, P not rational. Enumerate and also collect chi_2(N(y)).
        inert = []
        seen=set()
        for x1 in Fp2:
            rhs = x1**3 + A*x1 + B
            if not rhs.is_square(): continue
            y1 = rhs.sqrt()
            for sg in (1,-1):
                P = E2(x1, sg*y1)
                if P.is_zero(): continue
                phiP = E2(P[0]**p, P[1]**p)
                if (P + phiP) == R2 and not (P[0] in Fp):
                    if tuple(P) in seen: continue
                    seen.add(tuple(P))
                    Ny = P[1] * phiP[1]   # N(y_P) = y_P y_{phiP}
                    inert.append((P, chi2(Ny, p)))
        # is the coset really kerTr + P0 for some P0? Pick one inert point P0, check inert = P0 + kerTr (the non-rational part)
        if not inert: continue
        P0 = inert[0][0]
        coset_check = []
        for (K,_) in [(K,0) for K in kerTr]:
            Q = P0 + K
            # is Q inert with Tr(Q)=R? Tr(P0+K)=Tr(P0)+Tr(K)=R+O=R. And Q inert iff Q not in E(F_p).
            coset_check.append(tuple(Q))
        inert_set = set(t for (t,_) in inert)
        coset_set = set(coset_check)
        # the inert points = (P0 + kerTr) minus the rational points in that coset
        overlap = inert_set & coset_set
        print("\nR=[%d]G: %d inert points ; (P0+kerTr) has %d pts ; overlap %d"%(e, len(inert), len(coset_set), len(overlap)))

        # TEST: is chi_2(N(y_P)) a character of the coset? For K in kerTr, does chi_2(N(y_{P0+K})) factor?
        # i.e. is there a character chi(K) with chi_2(N(y_{P0+K})) = chi_2(N(y_{P0})) * chi(K)?
        # collect (K, chi_2(N(y_{P0+K}))) and see if it's a homomorphism K -> {+/-1}
        vals = []
        base = chi2(P0[1]*(E2(P0[0]**p,P0[1]**p))[1], p)
        for K in kerTr:
            Q = P0 + K
            if Q.is_zero(): continue
            phiQ = E2(Q[0]**p, Q[1]**p)
            Ny = Q[1]*phiQ[1]
            if Ny != Ny**p: continue
            cq = chi2(Ny, p)
            vals.append((K, cq))
        # is the map K -> cq a homomorphism? test: chi(K1+K2) == chi(K1)*chi(K2) for several pairs
        import itertools
        hom_ok = True; tested = 0
        Kmap = {}
        for (K,c) in vals: Kmap[tuple(K)] = c if c != 0 else None
        nonzero_vals = [(K,c) for (K,c) in vals if c != 0]
        for (K1,c1),(K2,c2) in itertools.islice(itertools.product(nonzero_vals, nonzero_vals), 200):
            Ksum = K1 + K2
            cs = Kmap.get(tuple(Ksum))
            if cs is None: continue
            tested += 1
            if cs != c1*c2:
                hom_ok = False; break
        print("  chi_2(N(y_{P0+K})) homomorphism on ker(Tr)? tested %d pairs, ok=%s"%(tested, hom_ok))
        # count of +1/-1 in the coset
        ps = sum(1 for (_,c) in vals if c==1); ms = sum(1 for (_,c) in vals if c==-1); zs = sum(1 for (_,c) in vals if c==0)
        print("  coset chi_2(N(y)) signs: +%d/-%d/0%d ; sum = %d"%(ps,ms,zs, ps-ms))
