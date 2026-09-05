#!/usr/bin/env sage
"""reduce26_S_of_e_probe_v1.sage -- identify S(e) = Sum_rat_distinct(e) = Sum_conj(e) as a function of e.

#26 <=> S(e) is well-defined (the two strata agree) for all e. Compute S(e) for ALL e in Z/n and ask:
is S(e) a recognizable object? Since S(e) = (1/2)((h1*h1)[e] - diagonal) and the diagonal is +1 only at
the unique e0 with 2[e0]G = [e]G (i.e. e0 = e/2 mod n, n odd so unique), S(e) is essentially the
convolution h1*h1 (minus a delta). Its DFT is (H1)^2 where H1 = DFT(h1) = -V1 (the eigenvalue sum).
So S(e) is the inverse-DFT of (V1)^2/4 up to the diagonal shift.

If V1(a) is itself a recognizable object (a Gauss sum?), then S = IDFT(V1^2) is its autocorrelation,
and #26 (S_conj = S_rat) would follow from a property of V1. Probe this concretely.
"""
from sage.all import GF, ZZ
import audit_n1_vsign_v2_core as core


def S_of_e_rat(p, n):
    """S(e) = sum over unordered distinct rational pairs {Q,Q'}, Q+Q'=[e]G, of chi_2(y_Q y_Q').
    = (1/2)[ (h1*h1)[e]  - (diagonal: the e0 with 2 e0 = e, contributing chi_2(y_P0)^2 = +1 if e0!=0, and O-handling) ].
    Direct: use h1*h1 and subtract the diagonal."""
    dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl)
    conv = core.polymul_mod_cyc(h1, h1, n)   # (h1*h1)[e] = sum_d h1[d]h1[e-d]
    # diagonal contribution at e: the unique e0 with 2*e0 = e mod n (n odd), if h1[e0] includes the P0
    # point with chi_2(y_P0). But h1[e0] = sum over F_p points at dlog e0 of chi_2(y). The diagonal of
    # the convolution at e is h1[e0]*h1[e0] only if e0 = e-e0 i.e. 2e0=e. The (h1*h1)[e] sum INCLUDES
    # the term d=e0, e-d=e0 i.e. h1[e0]^2. But we want only the PAIR {P0,P0} geometric contribution,
    # which is chi_2(y_P0)^2 = 1, NOT h1[e0]^2 (h1[e0] sums over ALL points at dlog e0). So the
    # "diagonal" in the GEOMETRIC sense is subtle. Cleanest: compute S(e) DIRECTLY by enumerating
    # rational pairs, not via the convolution.
    return None  # placeholder; compute directly below


def S_of_e_direct(p, A, B):
    """Compute S(e) for all e by direct enumeration of rational distinct pairs on E(F_p)."""
    from sage.all import EllipticCurve
    Fp = GF(p); E = EllipticCurve(Fp, [A, B]); n = E.order()
    G = next(P for P in E if P.order() == n)
    pts = [e*G for e in range(n)]   # [e]G for e=0..n-1 ; pts[0] = O
    # chi_2(y) for each point; O -> 0
    def psi(P):
        if P.is_zero(): return 0
        y = int(P[1]) % p
        if y == 0: return 0
        return 1 if pow(y, (p-1)//2, p) == 1 else -1
    psi_arr = [psi(pts[e]) for e in range(n)]   # psi([e]G)
    # S(e) = sum over d of psi_arr[d]*psi_arr[(e-d) % n], EXCLUDING d where [d]G or [e-d]G is O
    # (d=0 or e-d=0 i.e. d=e), and EXCLUDING the diagonal d = e-d i.e. 2d=e (d=e0).
    S = [0]*n
    for e in range(1, n):   # e=0 is R=O, skip
        s = 0
        for d in range(1, n):
            if d == e: continue   # Q' = O
            ed = (e - d) % n
            if ed == 0: continue  # Q = O
            if (2*d) % n == e: continue   # diagonal Q=Q'=P0, exclude (distinct pairs only)
            s += psi_arr[d] * psi_arr[ed]
        # each unordered pair {d, e-d} counted twice (d and e-d), so halve
        S[e] = s // 2
    return S, n, G, psi_arr


if __name__ == "__main__":
    p, A, B = 43, 0, 7
    S, n, G, psi_arr = S_of_e_direct(p, A, B)
    print("p=%d n=%d E:y^2=x^3+%d"%(p,n,B))
    print("psi([e]G) = chi_2(y) for e=1..%d:"%min(n-1,15), psi_arr[1:16])
    print("S(e) = Sum_rat_distinct(e) for e=1..%d:"%min(n-1,20), S[1:21])
    # is S(e) a multiplicative character of e? e is in Z/n (additive). Check if S factors through a
    # multiplicative character of <G> = Z/n. Test: is S(e) = c * lambda^e for some lambda? (geometric)
    #   => S(e+1)/S(e) should be constant where nonzero. Or check if S is supported on a coset.
    # Better: DFT of S. hat_S(a) = sum_e S(e) zeta_n^{-ae}. If S = (1/2)(h1*h1 - diag), hat_S = (1/2)(H1^2 - diag_hat).
    # but we computed S directly. Compute its DFT and compare to (V1)^2/4.
    # V1(a) = -e1(a) = sum_d h1[d] zeta^{ad}. Note h1[d] = psi([d]G) = psi_arr[d] (with h1[0]=0=psi(O)). Good.
    from sage.all import CyclotomicField
    K = CyclotomicField(n); z = K.gen()
    h1 = psi_arr[:]  # h1[0] = psi(O) = 0 already
    V1 = [sum(h1[d]*z**((a*d)%n) for d in range(n)) for a in range(n)]
    # DFT of S: hatS(a) = sum_e S[e] z^{-ae}
    hatS = [sum(S[e]*z**((-a*e)%n) for e in range(n)) for a in range(n)]
    # relation check: hatS(a) should be (V1(a)^2 - diag_term(a))/2
    print("\nDFT checks: hatS(a) vs (V1(a)^2)/2 for a=1..8:")
    for a in range(1,9):
        v1sq = V1[a]**2
        print("  a=%d: hatS=%s ; V1^2/2=%s ; equal? %s" % (a, hatS[a], v1sq/2, hatS[a] == v1sq/2))
    # Is V1(a) a Gauss sum? V1(a) = sum_d chi_2(y_{[d]G}) zeta^{ad}. Compare magnitude (should be sqrt(p) if Gauss-like)
    print("\n|V1(a)| for a=1..10 (sqrt(p)=%.4f if Gauss-sum-like):" % (p**0.5))
    for a in range(1,11):
        print("  a=%d: |V1|^2 = %s" % (a, V1[a]*V1[a].conjugate()))
    # NUMERICAL magnitudes via complex embedding
    emb = z.complex_embedding()
    V1num = [complex(sum(h1[d]*emb**((a*d)%n) for d in range(n))) for a in range(n)]
    print("\nNUMERICAL |V1(a)|^2 for a=1..15 (p=%d):" % p)
    for a in range(1,16):
        m = abs(V1num[a])**2
        print("  a=%2d: |V1|^2 = %8.4f   (= p%+d ?  = %.4f*%d ?)" % (a, m, m-p, m/p if p else 0, n))
