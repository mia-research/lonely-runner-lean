# anew_step3_witness_v1.sage
#
# PREREG: PREREG_anew_supersingularity_reaudit_v2.md, hypothesis H-A.
#
# Tests whether Step 3 of RESULT_mu6_cohomology_supersingular_v2.md excludes the
# ordinary stratum.  Step 3's ordinary case reads, verbatim:
#
#   "Ordinary (p-rank 2). End^0(A_new) is a commutative field (a quartic CM field).
#    Then pi i pi^-1 = i != -i.  Contradiction."
#
# Candidate witness: A = E x E^d over F_p, p = 3 mod 4, E ORDINARY, d a non-square.
#   psi : E^d -> E   the twisting isomorphism, defined over F_{p^2}, psi^sigma = -psi
#   i    : (P,Q) |-> (psi(Q), -psi^{-1}(P))          on A
#
# DECISION CONDITIONS (prereg v2 sec.1):
#   A1  psi is an isomorphism over F_{p^2}, NOT over F_p, and Frob.psi = -psi.Frob   [can fail]
#   A5  pi . i = (-i) . pi   pointwise                                              [can fail]
#   A3a a_p(E) != 0 mod p    (E ordinary)                                           [property of sample]
# INSTRUMENT CHECKS ONLY (derivations, cannot fail -- reported, never counted as evidence):
#   A2  i^2 = [-1]
#   A4  a_p(E^d) = -a_p(E)
#   A3b b_2(A) = 2p - a^2 != 0 mod p    (restates A3a)
#
# All arithmetic exact in finite fields.  No float.

import sys

SEED = 20260802
set_random_seed(SEED)

PRIMES = [7, 11, 19, 23, 31, 43, 67, 103, 127, 211]   # all = 3 mod 4
N_CURVES = 3
N_POINTS = 20

def least_nonsquare(p):
    for c in range(2, p):
        if not GF(p)(c).is_square():
            return GF(p)(c)
    raise RuntimeError("no non-square")

def frob_pt(C, P, p):
    if P.is_zero():
        return C(0)
    return C(P[0]**p, P[1]**p)

print("=" * 78)
print("H-A : ordinary witness against Step 3's ordinary-stratum exclusion")
print("PREREG PREREG_anew_supersingularity_reaudit_v2.md sec.1 ; seed %d" % SEED)
print("=" * 78)

rows = []
fail_A1 = fail_A5 = fail_A2 = fail_A4 = 0
n_tested = 0
n_skipped_ss = 0

for p in PRIMES:
    Fp = GF(p)
    d = least_nonsquare(p)
    made = 0
    tries = 0
    while made < N_CURVES and tries < 400:
        tries += 1
        a = Fp(ZZ.random_element(0, p))
        b = Fp(ZZ.random_element(0, p))
        if 4*a**3 + 27*b**2 == 0:
            continue
        E0 = EllipticCurve(Fp, [a, b])
        ap = p + 1 - E0.cardinality()
        # A3a : E must be ORDINARY.  Supersingular curves are excluded and counted.
        if ap % p == 0:
            n_skipped_ss += 1
            continue
        made += 1
        n_tested += 1

        Ed0 = EllipticCurve(Fp, [a*d**2, b*d**3])
        apd = p + 1 - Ed0.cardinality()

        # ---- A4 (derivation / instrument check) -------------------------------
        ok_A4 = (apd == -ap)
        if not ok_A4:
            fail_A4 += 1

        # ---- b1, b2 of A = E x E^d -------------------------------------------
        b1 = ap + apd
        b2 = 2*p - ap**2
        ok_A3b = (b2 % p != 0)

        # ---- A1 / A2 / A5 over F_{p^2} and F_{p^4} ---------------------------
        res_k = {}
        for k in (2, 4):
            K = GF(p**k, 'g')
            ud = K(d).sqrt()
            assert ud**2 == K(d)
            EK  = EllipticCurve(K, [K(a), K(b)])
            EdK = EllipticCurve(K, [K(a)*K(d)**2, K(b)*K(d)**3])

            def psi(Q):
                if Q.is_zero():
                    return EK(0)
                return EK(Q[0]/K(d), Q[1]/(K(d)*ud))

            def psi_inv(P):
                if P.is_zero():
                    return EdK(0)
                return EdK(K(d)*P[0], K(d)*ud*P[1])

            okA1 = okA2 = okA5 = True
            for _ in range(N_POINTS):
                P = EK.random_point()
                Q = EdK.random_point()
                # A1 : psi is a curve isomorphism  and  Frob o psi = -psi o Frob
                if psi(Q) not in EK:
                    okA1 = False
                if frob_pt(EK, psi(Q), p) != -psi(frob_pt(EdK, Q, p)):
                    okA1 = False
                if psi_inv(psi(Q)) != Q:
                    okA1 = False
                # A2 : i^2 = [-1]  on A ;  i(P,Q) = (psi(Q), -psi^{-1}(P))
                i1, i2 = psi(Q), -psi_inv(P)
                ii1, ii2 = psi(i2), -psi_inv(i1)
                if (ii1, ii2) != (-P, -Q):
                    okA2 = False
                # A5 : pi.i = (-i).pi
                lhs = (frob_pt(EK, i1, p), frob_pt(EdK, i2, p))
                pP, pQ = frob_pt(EK, P, p), frob_pt(EdK, Q, p)
                j1, j2 = psi(pQ), -psi_inv(pP)
                rhs = (-j1, -j2)
                if lhs != rhs:
                    okA5 = False
            res_k[k] = (okA1, okA2, okA5)

        # A1 also requires psi NOT defined over F_p: exhibit an F_p-point of E^d
        # whose image has a coordinate outside F_p.
        K2 = GF(p**2, 'g')
        ud2 = K2(d).sqrt()
        not_over_Fp = False
        for Q in Ed0.points()[:50]:
            if Q.is_zero():
                continue
            im_y = K2(Q[1])/(K2(d)*ud2)
            if im_y not in [K2(z) for z in Fp]:
                not_over_Fp = True
                break

        okA1 = all(res_k[k][0] for k in (2, 4)) and not_over_Fp
        okA2 = all(res_k[k][1] for k in (2, 4))
        okA5 = all(res_k[k][2] for k in (2, 4))
        if not okA1: fail_A1 += 1
        if not okA2: fail_A2 += 1
        if not okA5: fail_A5 += 1

        rows.append((p, a, b, ap, apd, b1, b2 % p, okA1, okA5, ok_A4, okA2, ok_A3b))
        print("p=%-5d E=[%s,%s]  a_p=%-5d a_p(E^d)=%-5d | b1=%-3d b2 mod p=%-5d | "
              "A1=%s A5=%s | A4=%s A2=%s A3b=%s"
              % (p, a, b, ap, apd, b1, b2 % p,
                 "PASS" if okA1 else "FAIL", "PASS" if okA5 else "FAIL",
                 "ok" if ok_A4 else "BROKEN", "ok" if okA2 else "BROKEN",
                 "ok" if ok_A3b else "BROKEN"))

print("-" * 78)
print("curves tested (ordinary)      : %d" % n_tested)
print("supersingular curves skipped  : %d" % n_skipped_ss)
print("A1 failures (can fail)        : %d" % fail_A1)
print("A5 failures (can fail)        : %d" % fail_A5)
print("A2 failures (instrument only) : %d" % fail_A2)
print("A4 failures (instrument only) : %d" % fail_A4)
print("all rows ordinary (b2 != 0)   : %s" % all(r[6] != 0 for r in rows))
print("all rows b1 == 0              : %s" % all(r[5] == 0 for r in rows))
verdict = (fail_A1 == 0 and fail_A5 == 0 and n_tested > 0)
print()
print("H-A DECISION (A1 and A5 both clean, >0 ordinary curves): %s"
      % ("UPHELD" if verdict else "NOT UPHELD"))
print("=" * 78)
