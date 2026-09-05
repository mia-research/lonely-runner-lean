#!/usr/bin/env python3
"""
collinear_lift_structure_v1.py — does the GROUP LAW couple to the lift geometry?

New object (never built). Prior probes: single-point (generic), 2-point difference set
(generic), joint (x,y) transform (mu3 + generic). Untouched = the 3-POINT group law
P1+P2+P3=O (collinearity), the structure under SUMMATION-POLYNOMIAL / index-calculus
thinking -- the actual ECDLP frontier. First place ADDITION can imprint on the lift.

Sharp test with an EXACT null: by the Cap Law each curve point is core (eps=0) with
prob 3/4 INDEPENDENTLY, so a random triple is all-core with prob (3/4)^3 = 27/64.
  Q: do COLLINEAR triples (P1+P2+P3=O) deviate from 27/64 / from Binomial(3,1/4) on
     the #flaps?  Deviation = the group law SEES the geometric label = a peek at the fence.
Naturally uses x AND y (collinearity via the slope (y2-y1)/(x2-x1)).

Method: sample collinear triples as (P, Q, -(P+Q)) for random curve P,Q (guaranteed
on-curve, guaranteed summing to O). Matched null = 3 INDEPENDENT random curve points,
sampled+scored by the identical code. Statistics:
  (1) all-core fraction         vs 27/64 and vs the matched null
  (2) #flaps distribution {0,1,2,3}  vs Binomial(3,1/4) and vs matched null (chi-square)
  (3) |z1+z2+z3|^2 / p           collinear vs null  (exact ell-sum in Z[omega])
Verdict by SCALING in p + matched null (not a single-p z). Exact signal path (eps is
exact integer; |.|^2 via exact Z[omega] norm). Float only in displayed ratios/chi2.
"""
import math, random
import numpy as np
from sympy import isprime
from hybrid_char_sum_v1 import find_point, padd, legendre, tonelli
from int1_frame_operator_v1 import build


def rand_point(p, rng):
    while True:
        x = rng.randrange(0, p)
        r = (x * x * x + 7) % p
        if r == 0:
            return (x, 0)
        if legendre(r, p) == 1:
            y = tonelli(r, p)
            return (x, y if rng.random() < 0.5 else (p - y) % p)


def neg(P, p):
    return None if P is None else (P[0], (-P[1]) % p)


def emul(z, w):
    a, b = z; c, d = w
    return (a * c - b * d, a * d + b * c - b * d)


def enorm(a, b):
    return a * a - a * b + b * b


def triple_score(x1, x2, x3, eis, eps):
    """#flaps in the triple, all-core bool, exact |z1+z2+z3|^2."""
    nf = sum(1 for x in (x1, x2, x3) if eps(x) != 0)
    Sa = Sb = 0
    for x in (x1, x2, x3):
        u, v = eis(x); Sa += u; Sb += v
    return nf, (nf == 0), enorm(Sa, Sb)


def run_prime(p, K, seed):
    eis, eps = build(p)
    rng = random.Random(seed)
    col_flapcount = [0, 0, 0, 0]; nul_flapcount = [0, 0, 0, 0]
    col_allcore = nul_allcore = 0
    col_sumnorm = []; nul_sumnorm = []
    nc = nn = 0
    for _ in range(K):
        # collinear triple: P, Q, -(P+Q)
        P = rand_point(p, rng); Q = rand_point(p, rng)
        R = padd(P, Q, p)
        if R is None:                       # P = -Q, degenerate (third point = O)
            continue
        P3 = neg(R, p)
        nf, ac, sn = triple_score(P[0], Q[0], P3[0], eis, eps)
        col_flapcount[nf] += 1; col_allcore += ac; col_sumnorm.append(sn); nc += 1
        # matched null: 3 independent random curve points
        A = rand_point(p, rng); B = rand_point(p, rng); C = rand_point(p, rng)
        nf2, ac2, sn2 = triple_score(A[0], B[0], C[0], eis, eps)
        nul_flapcount[nf2] += 1; nul_allcore += ac2; nul_sumnorm.append(sn2); nn += 1
    return {
        "p": p, "nc": nc, "nn": nn,
        "col_allcore": col_allcore / nc, "nul_allcore": nul_allcore / nn,
        "col_fc": np.array(col_flapcount) / nc, "nul_fc": np.array(nul_flapcount) / nn,
        "col_sumnorm_med": float(np.median(col_sumnorm)) / p,
        "nul_sumnorm_med": float(np.median(nul_sumnorm)) / p,
        "col_fc_raw": col_flapcount, "nul_fc_raw": nul_flapcount,
    }


def chi2_between(obs_a, obs_b):
    """chi-square comparing two count vectors (collinear vs null flap-distributions)."""
    a = np.array(obs_a, float); b = np.array(obs_b, float)
    Na, Nb = a.sum(), b.sum()
    # pooled expected proportion
    pool = (a + b) / (Na + Nb)
    ea = pool * Na; eb = pool * Nb
    chi = 0.0
    for o, e in list(zip(a, ea)) + list(zip(b, eb)):
        if e > 0:
            chi += (o - e) ** 2 / e
    return chi                                    # 3 dof


def main():
    print("COLLINEAR-TRIPLE lift structure : does the GROUP LAW (P1+P2+P3=O) see the")
    print("geometric core/flap label?   EXACT null: random triple all-core = (3/4)^3 = "
          f"{27/64:.4f};  #flaps ~ Binomial(3,1/4).")
    print("=" * 80)
    binom = np.array([(math.comb(3, k) * (1 / 4) ** k * (3 / 4) ** (3 - k)) for k in range(4)])
    print(f"Binomial(3,1/4) #flaps target: {np.round(binom,4)}\n")
    print(f"{'p':>6} {'K':>6} {'col allcore':>11} {'nul allcore':>11} {'chi2(col|nul)':>13} "
          f"{'col #flaps':>28} {'sumnorm col/nul':>16}")
    for p in [1009, 5011, 20011, 60013]:
        if not isprime(p) or p % 3 != 1:
            continue
        K = 40000
        r = run_prime(p, K, seed=p)
        chi = chi2_between(r["col_fc_raw"], r["nul_fc_raw"])
        fc = np.round(r["col_fc"], 4)
        print(f"{p:>6} {r['nc']:>6} {r['col_allcore']:>11.4f} {r['nul_allcore']:>11.4f} "
              f"{chi:>13.2f} {str(fc):>28} {r['col_sumnorm_med']:.3f}/{r['nul_sumnorm_med']:.3f}")
    print()
    print("READ: col-allcore ~ nul-allcore ~ 0.4219 and chi2(3dof) small & flat in p")
    print("      => group law does NOT see the label (generic).  A GROWING chi2, or")
    print("      col-allcore drifting from 27/64 with p, = group-law/geometry coupling (gate).")


if __name__ == "__main__":
    main()
