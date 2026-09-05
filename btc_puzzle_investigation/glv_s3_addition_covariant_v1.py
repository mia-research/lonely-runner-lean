#!/usr/bin/env python3
"""
glv_s3_addition_covariant_v1.py

The group law as its ACTUAL CM-covariant constraint -- the third summation
polynomial S3, not the wrong additive baseline U_S - U_P - U_Q.

For y^2 = x^3 + b, the third summation polynomial in x_S is a QUADRATIC:
    S3(x1,x2,x3) = A x3^2 + B x3 + C,
    A = (x1-x2)^2,
    B = -2((x1+x2) x1 x2 + 2b),
    C = (x1 x2)^2 - 4 b (x1+x2).
Its two roots are exactly { x_{P+Q}, x_{P-Q} }.  Hence the SYMMETRIC functions
    sigma1 = x_{P+Q} + x_{P-Q} = -B/A,
    sigma2 = x_{P+Q} . x_{P-Q} =  C/A
are RATIONAL in (x_P, x_Q) alone -- computable with NO y and NO discrete log:
the y-free part of the group law.

CM structure (from S3 [omega]-covariant, eigenvalue beta^1):
    sigma1(beta x_P, beta x_Q) = beta . sigma1(x_P, x_Q)   (weight-1: a COORDINATE)
    sigma2(beta x_P, beta x_Q) = beta^2 . sigma2            (weight-2)
So sigma1 obeys the SAME lift endomorphism law as any x-coordinate, and its
mu3-orbit label eps(sigma1) is well defined.

THE TEST (the addition-law label question, done on the correct covariant object):
  does (label(x_P), label(x_Q)) predict label(sigma1) / label(sigma2)?
with matched-null MI + population scaling + shuffle control.  A label
homomorphism on the y-free covariant coordinate = a group-tracking invariant
computable from x_P,x_Q alone = a real handle.  Flat/declining z = scoped null.

Validation built in: sigma1,sigma2 recomputed as the actual x(P+Q),x(P-Q)
symmetric functions (must match the S3 quadratic), and beta-covariance checked.
Exact integers mod p in the whole signal path.
"""
import math
import random
from collections import Counter

from glv_fundamental_domain_law_v1 import (make_lift, sextant, cube_roots,
                                           P_SECP, AP_SECP, BP_SECP)
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce
from glv_three_point_lift_v1 import ec_add, rand_point

P = P_SECP
B = 7


def om2(w):
    u, v = w
    return (v - u, -u)


def neg(Pt):
    return None if Pt is None else (Pt[0], (-Pt[1]) % P)


def s3_sigmas(x1, x2):
    """sigma1=-B/A, sigma2=C/A of the S3 quadratic in x3; None if A=0 (x1==x2)."""
    A = (x1 - x2) ** 2 % P
    if A == 0:
        return None
    Bc = (-2 * ((x1 + x2) * x1 % P * x2 % P + 2 * B)) % P
    Cc = ((x1 * x2) ** 2 - 4 * B * (x1 + x2)) % P
    Ainv = pow(A, P - 2, P)
    return ((-Bc) * Ainv % P, Cc * Ainv % P)


def mi_bits_pair(fs, ts, nf, nt):
    J = [[0] * nt for _ in range(nf)]
    for a, b in zip(fs, ts):
        J[a][b] += 1
    tot = len(fs)
    rs = [sum(r) for r in J]
    cs = [sum(J[i][j] for i in range(nf)) for j in range(nt)]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
               for i in range(nf) for j in range(nt) if J[i][j] and rs[i] and cs[j])


def main():
    R1, R2 = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    R1, R2, DET, reduce_P, eis = make_lift(P, R1, R2)
    b1, b2 = cube_roots(P)
    beta = b1 if eis((b1 * 12345) % P) == reduce_P(*om2(eis(12345))) else b2
    R1t, R2t = tuple(R1), tuple(R2)

    def eps_of_x(x):
        U0 = eis(x); U1 = eis((beta * x) % P)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0):
            return 1
        if c == R1t or c == R2t:
            return 2
        if c == (-R1t[0], -R1t[1]) or c == (-R2t[0], -R2t[1]):
            return 0
        return 3

    print("=" * 74)
    print("S3 addition constraint: label law of the y-free covariant coordinate sigma1")
    print("=" * 74)

    # ---- validation: sigma1,sigma2 == symmetric functions of x(P+Q),x(P-Q);
    #      and beta-covariance sigma1(bx1,bx2)=b.sigma1 ----
    rng = random.Random(4321)
    val_ok = cov_ok = val_tot = 0
    while val_tot < 400:
        P1 = rand_point(P, rng); P2 = rand_point(P, rng)
        if P1[0] == P2[0]:
            continue
        R = ec_add(P1, P2, P); D = ec_add(P1, neg(P2), P)
        if R is None or D is None:
            continue
        sig = s3_sigmas(P1[0], P2[0])
        if sig is None:
            continue
        val_tot += 1
        s1_true = (R[0] + D[0]) % P
        s2_true = (R[0] * D[0]) % P
        if sig == (s1_true, s2_true):
            val_ok += 1
        sigb = s3_sigmas(beta * P1[0] % P, beta * P2[0] % P)
        if sigb and sigb[0] == beta * sig[0] % P and sigb[1] == pow(beta, 2, P) * sig[1] % P:
            cov_ok += 1
    print(f"  validation: sigma == symm.fns of x(P+Q),x(P-Q): {val_ok}/{val_tot}")
    print(f"  beta-covariance sigma1->b.sigma1, sigma2->b^2.sigma2: {cov_ok}/{val_tot}\n")

    # ---- collect labels for the homomorphism test ----
    NMAX = 90000
    recs = []
    while len(recs) < NMAX:
        P1 = rand_point(P, rng); P2 = rand_point(P, rng)
        if P1[0] == P2[0]:
            continue
        sig = s3_sigmas(P1[0], P2[0])
        if sig is None or 0 in sig:
            continue
        s1, s2 = sig
        recs.append((eps_of_x(P1[0]), eps_of_x(P2[0]), eps_of_x(s1),
                     sextant(*eis(P1[0])), sextant(*eis(P2[0])),
                     sextant(*eis(s1)), eps_of_x(s2), sextant(*eis(s2))))
    M = len(recs)
    mc = Counter(r[2] for r in recs)
    print(f"  M={M}   eps(sigma1) marginal 0-core:{mc[1]/M:.4f} +:{mc[2]/M:.4f} "
          f"-:{mc[0]/M:.4f} other:{mc[3]/M:.4f}  (single-pt law 3/4:1/8:1/8)\n")

    def hom_test(name, fx, nf, tx, nt, seed):
        rr = random.Random(seed)
        print("-" * 74)
        print(f"({name})")
        print("-" * 74)
        for NN in [M // 4, M // 2, M]:
            f = fx[:NN]; t = tx[:NN]
            obs = mi_bits_pair(f, t, nf, nt)
            nulls = []
            for _ in range(200):
                sh = t[:]; rr.shuffle(sh)
                nulls.append(mi_bits_pair(f, sh, nf, nt))
            mu = sum(nulls) / len(nulls)
            sd = (sum((q - mu) ** 2 for q in nulls) / len(nulls)) ** 0.5
            z = (obs - mu) / sd if sd else 0.0
            print(f"    N={NN:6d}: MI={obs:.5f} null={mu:.5f} z={z:+6.2f}")
        # control: shuffle target once, then test (must read ~0)
        ct = tx[:]; rr.shuffle(ct)
        obs = mi_bits_pair(fx, ct, nf, nt)
        cn = []
        for _ in range(200):
            sh = ct[:]; rr.shuffle(sh)
            cn.append(mi_bits_pair(fx, sh, nf, nt))
        cmu = sum(cn) / len(cn); csd = (sum((q - cmu) ** 2 for q in cn) / len(cn)) ** 0.5
        print(f"    CONTROL z = {(obs-cmu)/csd if csd else 0.0:+.2f}  (must be ~0)")

    # eps codes -1..2 already mapped to 0..3 by eps_of_x
    epsP = [r[0] for r in recs]; epsQ = [r[1] for r in recs]
    keyE = [a * 4 + b for a, b in zip(epsP, epsQ)]
    keyS = [a * 6 + b for a, b in zip((r[3] for r in recs), (r[4] for r in recs))]

    hom_test("(eps_P,eps_Q) -> eps(sigma1)  [y-free covariant coord label law]",
             keyE, 16, [r[2] for r in recs], 4, 11)
    hom_test("(sextant_P,sextant_Q) -> sextant(sigma1)",
             keyS, 36, [r[5] for r in recs], 6, 12)
    hom_test("(eps_P,eps_Q) -> eps(sigma2)  [weight-2 companion]",
             keyE, 16, [r[6] for r in recs], 4, 13)

    print("\n" + "=" * 74)
    print("Verdict rule: label homomorphism needs MI>>null AND z growing ~sqrt(N)")
    print("AND control~0.  sigma1 is the CORRECT covariant addition coordinate; a")
    print("law here would be group-tracking from x_P,x_Q alone.  Flat = scoped null.")


if __name__ == "__main__":
    main()
