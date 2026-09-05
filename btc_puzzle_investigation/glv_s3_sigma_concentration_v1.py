#!/usr/bin/env python3
"""
glv_s3_sigma_concentration_v1.py

Escalation of glv_s3_addition_covariant_v1 from LABEL resolution to FULL resolution.
The label law (eps/sextant of x_P,x_Q -> label of sigma1) was flat.  Now: is there
a FIXED Z[omega] combination of the lifts U_P=eis(x_P), U_Q=eis(x_Q),
U_s=eis(sigma1) that is BOUNDED -- i.e. takes FEW DISTINCT VALUES (the way the
endomorphism correction eis(bX)-omega^2 eis(X) collapses to {0,+-R}, distinct=5,
top-mass ~0.75)?  A bounded combination = the group law linearizing in the lift =
a real handle.

Two parts, exact integers in the whole lift/combination path:

 (A) BOUNDEDNESS of fixed Z[omega] combinations of (U_P,U_Q,U_s): distinct-count,
     top-mass, median N-bits of the RAW value (NOT reduced -- boundedness = few
     distinct values, cf. +-R is ~2^128 in size but the SET has 5 elements).
     Baseline for calibration: the single-coordinate endo correction (distinct 5).
     A-priori: linear forms should all scale ~2^128 (no exact linear identity for a
     nonlinear sigma1) -- we MEASURE this rather than assume it.

 (B) FINE-GRID conditioning: bin each lift into a k x k grid of the fundamental
     domain (exact fractional basis coords) and test (cell(U_P),cell(U_Q)) ->
     cell(U_s) at k=4,8 with matched-null MI + population scaling + shuffle control.
     Growing z with resolution AND N = structure between coarse label and full
     resolution.  Flat = the null deepens (scoped, not closure).
"""
import math
import random
from collections import Counter
from fractions import Fraction as F

from glv_fundamental_domain_law_v1 import (make_lift, sextant, cube_roots,
                                           P_SECP, AP_SECP, BP_SECP)
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce, enorm
from glv_three_point_lift_v1 import ec_add, rand_point

P = P_SECP
B = 7


def om(w):
    u, v = w
    return (-v, u - v)


def om2(w):
    u, v = w
    return (v - u, -u)


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def s3_sigma1(x1, x2):
    A = (x1 - x2) ** 2 % P
    if A == 0:
        return None
    Bc = (-2 * ((x1 + x2) * x1 % P * x2 % P + 2 * B)) % P
    return (-Bc) * pow(A, P - 2, P) % P


def mi_bits_pair(fs, ts, nf, nt):
    J = [[0] * nt for _ in range(nf)]
    for a, b in zip(fs, ts):
        J[a][b] += 1
    tot = len(fs)
    rs = [sum(r) for r in J]
    cs = [sum(J[i][j] for i in range(nf)) for j in range(nt)]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))  # noqa: float
               for i in range(nf) for j in range(nt) if J[i][j] and rs[i] and cs[j])


def main():
    R1, R2 = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    R1, R2, DET, reduce_P, eis = make_lift(P, R1, R2)
    b1, b2 = cube_roots(P)
    beta = b1 if eis((b1 * 12345) % P) == reduce_P(*om2(eis(12345))) else b2

    def frac_coords(U):
        c1 = F(U[0] * R2[1] - U[1] * R2[0], DET)
        c2 = F(U[1] * R1[0] - U[0] * R1[1], DET)
        return c1, c2

    def cell(U, k):
        c1, c2 = frac_coords(U)
        a = int((c1 + F(1, 2)) * k) % k
        b = int((c2 + F(1, 2)) * k) % k
        return a * k + b

    print("=" * 74)
    print("sigma1 concentration at FULL resolution (Z[omega] combos + fine grid)")
    print("=" * 74)

    NMAX = 60000
    rng = random.Random(112358)
    UP = []; UQ = []; US = []
    while len(UP) < NMAX:
        P1 = rand_point(P, rng); P2 = rand_point(P, rng)
        if P1[0] == P2[0]:
            continue
        s1 = s3_sigma1(P1[0], P2[0])
        if s1 is None or s1 == 0:
            continue
        UP.append(eis(P1[0])); UQ.append(eis(P2[0])); US.append(eis(s1))
    M = len(UP)
    print(f"  samples M={M}\n")

    # calibration baseline: single-coordinate endo correction distinct/top-mass
    # (fresh x for a clean {0,+-R} 5-set baseline)
    cc = Counter()
    for _ in range(M):
        x = rng.randrange(1, P)
        U0 = eis(x); U1 = eis((beta * x) % P)
        cc[sub(U1, om2(U0))] += 1
    print("-" * 74)
    print("CALIBRATION: single-coord endo correction eis(bX)-w^2 eis(X)")
    print(f"    distinct={len(cc)}  top-mass={max(cc.values())/M:.4f}   "  # noqa: float
          f"(the {{0,+-R}} bounded set: distinct~5, top~0.75)")

    # ---- (A) boundedness of fixed Z[omega] combos of (U_P,U_Q,U_s) ----
    print("\n" + "-" * 74)
    print("(A) boundedness of fixed Z[omega] combos  (bounded <=> few distinct)")
    print("-" * 74)
    combos = {
        "U_s - U_P - U_Q": lambda p, q, s: sub(sub(s, p), q),
        "U_s - w(U_P+U_Q)": lambda p, q, s: sub(s, om(add(p, q))),
        "U_s - w^2(U_P+U_Q)": lambda p, q, s: sub(s, om2(add(p, q))),
        "U_s - w U_P - w^2 U_Q": lambda p, q, s: sub(sub(s, om(p)), om2(q)),
        "w U_s - U_P - U_Q": lambda p, q, s: sub(sub(om(s), p), q),
        "U_s + U_P + U_Q": lambda p, q, s: add(add(s, p), q),
    }
    for name, fn in combos.items():
        vals = Counter(fn(UP[i], UQ[i], US[i]) for i in range(M))
        # median N-bits over samples
        allmag = sorted(enorm(fn(UP[i], UQ[i], US[i])) for i in range(M))
        med_bits = allmag[M // 2].bit_length()
        print(f"    {name:24s}: distinct={len(vals):6d}  top-mass={max(vals.values())/M:.5f}"  # noqa: float
              f"  median N-bits={med_bits}")
    print("    (distinct~M, top~1/M, N-bits~256 => spread/no linearization;")
    print("     distinct small + high top-mass => a bounded law, escalate hard)")

    # ---- (B) fine-grid conditioning with scaling + control ----
    print("\n" + "-" * 74)
    print("(B) fine-grid (cell(U_P),cell(U_Q)) -> cell(U_s), matched null + scaling")
    print("-" * 74)
    for k in (4, 8):
        cP = [cell(u, k) for u in UP]
        cQ = [cell(u, k) for u in UQ]
        cS = [cell(u, k) for u in US]
        nf = (k * k) ** 2
        key = [a * (k * k) + b for a, b in zip(cP, cQ)]
        rr = random.Random(1000 + k)
        print(f"  k={k}  ({k*k} cells/lift, {nf} key cells):")
        for NN in [M // 4, M // 2, M]:
            f = key[:NN]; t = cS[:NN]
            obs = mi_bits_pair(f, t, nf, k * k)
            nulls = []
            for _ in range(80):
                sh = t[:]; rr.shuffle(sh)
                nulls.append(mi_bits_pair(f, sh, nf, k * k))
            mu = sum(nulls) / len(nulls)  # noqa: float
            sd = (sum((q - mu) ** 2 for q in nulls) / len(nulls)) ** 0.5  # noqa: float
            z = (obs - mu) / sd if sd else 0.0  # noqa: float
            print(f"     N={NN:6d}: MI={obs:.4f} null={mu:.4f} z={z:+6.2f}")
        # control
        ct = cS[:]; rr.shuffle(ct)
        obs = mi_bits_pair(key, ct, nf, k * k)
        cn = [mi_bits_pair(key, (lambda s: (rr.shuffle(s), s)[1])(ct[:]), nf, k * k)
              for _ in range(80)]
        cmu = sum(cn) / len(cn); csd = (sum((q - cmu) ** 2 for q in cn) / len(cn)) ** 0.5  # noqa: float
        print(f"     CONTROL z = {(obs-cmu)/csd if csd else 0.0:+.2f}  (must be ~0)")  # noqa: float

    print("\n" + "=" * 74)
    print("Reading: any bounded combo (A) or z growing with BOTH k and N (B) = the")
    print("group law concentrating in the lift at full resolution. Flat both = the")
    print("scoped null deepens to full resolution (still not closure).")


if __name__ == "__main__":
    main()
