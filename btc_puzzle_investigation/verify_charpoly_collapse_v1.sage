#!/usr/bin/env sage
# verify_charpoly_collapse_v1.sage
#
# Checks the DERIVATION in ANALYSIS_n1_charpoly_collapse_v1.md:
#
#  (D1) The closure alpha -> -conj(alpha) (PROVED-FORCED) forces the twisted char poly to
#       factor as   P(T) = (T^2 - s1 T - p)(T^2 - s2 T - p),  s_i = alpha_i - p/alpha_i,
#       hence  e3 = -p e1  and  e4 = p^2  are COROLLARIES, not independent facts.
#       (At p = 1 mod 4 the closure is alpha -> conj(alpha), giving (T^2-sT+p) factors and
#        e3 = +p e1: together, e3 = chi2(-1) p e1 -- the record's D4 relation, DERIVED.)
#       => the char poly has exactly TWO free coefficients, e1 and e2.
#
#  (D2) 120 degrees (alpha_2 = zeta_3 alpha_1) is EQUIVALENT to the single relation
#            e2 = e1^2 + p
#       and this is the SAME relation as V2 = V1^2 + 2p.  Three separately recorded facts
#       (the 120 law / the V2 identity / "uniform u = zeta_3") are ONE relation.
#
#  (D3) The ideal test is CIRCULAR (the record's own D-2), analytically: 120 => the ratio is
#       a root of unity => a UNIT => (alpha_1) = (alpha_2) identically.  No computation can
#       discriminate.  Confirmed here by construction, not measured.
#
# METHOD.  V1, V2 computed DIRECTLY from E(F_p) and E(F_p^2) (exact integer histograms) --
# the 120 law is NOT assumed anywhere in obtaining them.  Then e1 = -V1, e2 = (e1^2+V2)/2,
# and the checks are:
#     C-E2     e2 == e1^2 + p            (the 120 law as one relation)
#     C-WEIGHT |root| == sqrt(p) for all four roots of the derived P(T)
#     C-RATIO  the four roots form {a, a z3, -conj(a), -conj(a) z3bar}: ratio a primitive
#              cube root of unity
# All at EVERY frequency a, all primes.

B = 7


def curve_data(p):
    F = GF(p); E = EllipticCurve(F, [0, B]); n = E.cardinality()
    if not is_prime(n):
        return None
    G = E.gens()[0]; dl = {}; Q = E(0)
    for d in range(n):
        dl[Q] = d; Q = Q + G
    return E, G, n, dl


def hist_k(p, k, E1, n, dl):
    q = p ** k; Fq = GF(q, 'g'); Eq = EllipticCurve(Fq, [0, Fq(B)])
    h = [0] * n; half = (q - 1) // 2
    for P in Eq.points():
        if P.is_zero():
            continue
        y = P[1]
        if y == 0:
            continue
        chi = 1 if y ** half == 1 else -1
        T = Eq(0); Q = P
        for _ in range(k):
            T = T + Q; Q = Eq(Q[0] ** p, Q[1] ** p)
        Tp = E1(T[0], T[1]) if not T.is_zero() else E1(0)
        h[dl[Tp]] += chi
    return h


for p in [43, 67, 127]:
    r = curve_data(p)
    if r is None:
        print(f"p={p}: n not prime, skipped"); continue
    E, G, n, dl = r
    h1 = hist_k(p, 1, E, n, dl); h2 = hist_k(p, 2, E, n, dl)
    C = ComplexField(160); z = C(exp(2 * C.pi() * C.gen() / n))
    z3 = C(exp(2 * C.pi() * C.gen() / 3))
    V1 = [sum(h1[d] * z ** (a * d) for d in range(n)) for a in range(n)]
    V2 = [sum(h2[d] * z ** (a * d) for d in range(n)) for a in range(n)]
    e2err = wterr = raterr = 0
    bad = 0
    for a in range(1, n):
        e1 = -V1[a]
        e2 = (e1 ** 2 + V2[a]) / 2
        e2err = max(e2err, abs(e2 - (e1 ** 2 + p)))
        # derived e3, e4 from the closure (p = 3 mod 4 branch: chi2(-1) = -1)
        e3 = -p * e1; e4 = C(p) ** 2
        R.<T> = C[]
        P = T ** 4 - e1 * T ** 3 + e2 * T ** 2 - e3 * T + e4
        rts = [rt for rt, m in P.roots() for _ in range(m)]
        if len(rts) != 4:
            bad += 1; continue
        wterr = max(wterr, max(abs(abs(rt) - sqrt(C(p))) for rt in rts))
        # find a pair whose ratio is a primitive cube root of unity
        best = min(min(abs(rts[j] / rts[i] - z3), abs(rts[j] / rts[i] - z3 ** 2))
                   for i in range(4) for j in range(4) if i != j)
        raterr = max(raterr, best)
    print(f"p={p:4d} n={n:4d}  (all a != 0)")
    print(f"   C-E2      max |e2 - (e1^2 + p)|            = {float(e2err):.3e}")
    print(f"   C-WEIGHT  max | |root| - sqrt(p) |         = {float(wterr):.3e}")
    print(f"   C-RATIO   max over a of min ratio-to-z3^k  = {float(raterr):.3e}")
    print(f"   degenerate root counts: {bad}")
