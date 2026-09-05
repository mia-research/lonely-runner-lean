#!/usr/bin/env python3
"""
glv_addition_lift_conditioned_v1.py

The point-ADDITION lift law, CONDITIONED on CM labels of the summands.

Motivation.  eis linearizes MULTIPLICATION: the endomorphism law
  eis(beta X) = omega^2 . eis(X) + c,   c in {0, +-R},   dens 3/4:1/8:1/8
is exact and orbit-invariant.  The one operation the lift does NOT already
linearize is point ADDITION (= the DLP-bearing operation).  glv_three_point_lift
measured the naive additive correction c3 = reduce_P(U_S - U_P - U_Q) GLOBALLY
and found it "spread".  But the endomorphism correction was ALSO globally spread
("~98% orbit-sextant parity") until it was CONDITIONED on the mu3-orbit label.
This script asks the analogous question for addition:

  Is there a cheaply-computable CM label L(.) of a curve point such that
  L(P (+) Q) is PREDICTED by (L(P), L(Q))?    [a label homomorphism => a
  group-tracking invariant computable from x alone => a genuine handle]

We test three candidate labels -- sextant s in Z/6, the mu3-orbit label
eps in {0,+,-}, and a norm-band bucket -- with:
  (1) exact contingency  (L_P, L_Q) -> L_S,
  (2) matched-shuffle MI null,
  (3) POPULATION SCALING (z ~ sqrt(N) for a real effect, flat for sampling noise),
  (4) the full additive correction c3 CONDITIONED per (eps_P, eps_Q) and (s_P,s_Q)
      cell -- does any cell concentrate while the global census is spread?

Nothing is pre-judged: a global-spread correction can hide a per-cell law (that
is exactly how the endomorphism law was found).  Exact integers in the entire
point/lift/label path; float appears only in the MI/z statistic, which is a
monotone rank statistic compared to a MATCHED permutation null (no float decides
a verdict).  Control: the matched shuffle IS the null; its z must stay ~0.
"""
import math
import random
from collections import Counter
from fractions import Fraction as F

from glv_fundamental_domain_law_v1 import (make_lift, sextant, cube_roots,
                                           P_SECP, AP_SECP, BP_SECP)
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce, enorm
from glv_three_point_lift_v1 import ec_add, rand_point


def om(w):
    u, v = w
    return (-v, u - v)


def om2(w):
    u, v = w
    return (v - u, -u)


def build_secp_lift():
    R1, R2 = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    R1, R2, DET, reduce_P, eis = make_lift(P_SECP, R1, R2)
    b1, b2 = cube_roots(P_SECP)
    beta = b1 if eis((b1 * 12345) % P_SECP) == reduce_P(*om2(eis(12345))) else b2
    R1t, R2t = tuple(R1), tuple(R2)

    def eps_label(x):
        """mu3-orbit label of x: 0 (core / rigid) or +-1 (flap), from the endo correction."""
        U0 = eis(x)
        U1 = eis((beta * x) % P_SECP)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0):
            return 0
        if c == R1t or c == R2t:
            return 1
        if c == (-R1t[0], -R1t[1]) or c == (-R2t[0], -R2t[1]):
            return -1
        return 2  # other lattice correction (rare boundary)

    # norm-band buckets from the universal breakpoints s = N/p in [0,3/16,1/4,3/4]
    def norm_bucket(x):
        u, v = eis(x)
        s = F(enorm((u, v)), P_SECP)  # exact rational in [0,3/4]
        if s < F(3, 16):
            return 0
        if s < F(1, 4):
            return 1
        return 2

    return eis, reduce_P, eps_label, norm_bucket, beta


def mi_bits(J):
    tot = sum(sum(r) for r in J)
    if not tot:
        return 0.0
    rs = [sum(r) for r in J]
    cs = [sum(J[i][j] for i in range(len(J))) for j in range(len(J[0]))]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
               for i in range(len(J)) for j in range(len(J[0]))
               if J[i][j] and rs[i] and cs[j])


def scaled_mi_test(pairs, nlab, seed, ns):
    """pairs = list of ((lP,lQ), lS). Return per-N (obs, mu, sd, z) with matched
    shuffle null.  A real effect: obs>>null and z grows ~sqrt(N). Noise: z flat."""
    rng = random.Random(seed)
    out = []
    for N in ns:
        sub = pairs[:N]
        key = [k for k, _ in sub]
        tgt = [t for _, t in sub]
        J = [[0] * nlab for _ in range(nlab * nlab)]
        for (a, b), c in zip(key, tgt):
            J[a * nlab + b][c] += 1
        obs = mi_bits(J)
        nulls = []
        for _ in range(120):
            sh = tgt[:]
            rng.shuffle(sh)
            Jn = [[0] * nlab for _ in range(nlab * nlab)]
            for (a, b), c in zip(key, sh):
                Jn[a * nlab + b][c] += 1
            nulls.append(mi_bits(Jn))
        mu = sum(nulls) / len(nulls)
        sd = (sum((v - mu) ** 2 for v in nulls) / len(nulls)) ** 0.5
        z = (obs - mu) / sd if sd else 0.0
        out.append((N, obs, mu, sd, z))
    return out


def main():
    print("=" * 74)
    print("Point-ADDITION lift law, CONDITIONED on CM labels (secp256k1)")
    print("=" * 74)
    eis, reduce_P, eps_label, norm_bucket, beta = build_secp_lift()

    rng = random.Random(20260714)
    NMAX = 48000
    recs = []   # (sP,sQ,sS, eP,eQ,eS, bP,bQ,bS, c3)
    tries = 0
    while len(recs) < NMAX and tries < NMAX * 4:
        tries += 1
        P1 = rand_point(P_SECP, rng)
        P2 = rand_point(P_SECP, rng)
        if P1[0] == P2[0]:
            continue
        S = ec_add(P1, P2, P_SECP)
        if S is None:
            continue
        xP, xQ, xS = P1[0], P2[0], S[0]
        if 0 in (xP, xQ, xS):
            continue
        UP, UQ, US = eis(xP), eis(xQ), eis(xS)
        sP, sQ, sS = sextant(*UP), sextant(*UQ), sextant(*US)
        eP, eQ, eS = eps_label(xP), eps_label(xQ), eps_label(xS)
        bP, bQ, bS = norm_bucket(xP), norm_bucket(xQ), norm_bucket(xS)
        c3 = reduce_P(US[0] - UP[0] - UQ[0], US[1] - UP[1] - UQ[1])
        recs.append((sP, sQ, sS, eP, eQ, eS, bP, bQ, bS, c3))
    M = len(recs)
    print(f"\nsamples M = {M}  (independent random point pairs, S = P (+) Q)\n")

    ns = [M // 4, M // 2, M]

    # ---- (1) sextant homomorphism test: (s_P,s_Q) -> s_S ----
    print("-" * 74)
    print("(1) does (sextant_P, sextant_Q) predict sextant_S ?   [label in Z/6]")
    print("-" * 74)
    pr = [((r[0], r[1]), r[2]) for r in recs]
    for N, obs, mu, sd, z in scaled_mi_test(pr, 6, 1, ns):
        print(f"    N={N:6d}: MI={obs:.5f}  null={mu:.5f}+-{sd:.5f}  z={z:+6.1f}")
    print("    (real effect: MI>>null and z grows ~sqrt(N); sampling noise: z flat, MI~null)")

    # ---- (2) eps homomorphism test: (eps_P, eps_Q) -> eps_S ----
    print("\n" + "-" * 74)
    print("(2) does (eps_P, eps_Q) predict eps_S ?   [mu3-orbit label; the one that")
    print("    cracked the ENDOmorphism law -- first test of it under ADDITION]")
    print("-" * 74)
    # remap eps {-1,0,1,2} -> {0,1,2,3}
    rm = {-1: 0, 0: 1, 1: 2, 2: 3}
    pr = [((rm[r[3]], rm[r[4]]), rm[r[5]]) for r in recs]
    # marginal of eps
    mc = Counter(r[5] for r in recs)
    print(f"    eps_S marginal: 0(core):{mc[0]/M:.4f} +:{mc[1]/M:.4f} "
          f"-:{mc[-1]/M:.4f} other:{mc[2]/M:.4f}   (single-point law: 3/4:1/8:1/8)")
    for N, obs, mu, sd, z in scaled_mi_test(pr, 4, 2, ns):
        print(f"    N={N:6d}: MI={obs:.5f}  null={mu:.5f}+-{sd:.5f}  z={z:+6.1f}")

    # ---- (3) norm-bucket homomorphism test ----
    print("\n" + "-" * 74)
    print("(3) does (normband_P, normband_Q) predict normband_S ?   [label in {0,1,2}]")
    print("-" * 74)
    pr = [((r[6], r[7]), r[8]) for r in recs]
    for N, obs, mu, sd, z in scaled_mi_test(pr, 3, 3, ns):
        print(f"    N={N:6d}: MI={obs:.5f}  null={mu:.5f}+-{sd:.5f}  z={z:+6.1f}")

    # ---- (4) full additive correction c3, CONDITIONED on (eps_P,eps_Q) ----
    print("\n" + "-" * 74)
    print("(4) additive correction c3 = reduce_P(U_S - U_P - U_Q):")
    print("    GLOBAL census vs PER-CELL (eps_P,eps_Q) census.  Does any cell")
    print("    concentrate (small-set law) while the global is spread?")
    print("-" * 74)
    gl = Counter(r[9] for r in recs)
    print(f"    GLOBAL: distinct={len(gl)} (of M={M})  top-mass={max(gl.values())/M:.5f}")
    print(f"    per-cell (eps_P,eps_Q): distinct / topmass / count")
    cells = {}
    for r in recs:
        cells.setdefault((r[3], r[4]), Counter())[r[9]] += 1
    for k in sorted(cells):
        c = cells[k]
        tot = sum(c.values())
        if tot < 200:
            continue
        print(f"      eps={str(k):9s}: distinct={len(c):5d}  "
              f"top-mass={max(c.values())/tot:.5f}  (n={tot})")
    print("    (if every cell's top-mass ~ 1/distinct ~ 0, addition does NOT")
    print("     linearize in the lift even conditioned; a concentrated cell = a law)")

    # ---- (4b) same, conditioned on (s_P,s_Q) coarser but larger cells ----
    print("\n    conditioned on (sextant_P, sextant_Q) [36 cells], top-mass summary:")
    cells2 = {}
    for r in recs:
        cells2.setdefault((r[0], r[1]), Counter())[r[9]] += 1
    tms = sorted((max(c.values()) / sum(c.values()), k) for k, c in cells2.items()
                 if sum(c.values()) >= 200)
    if tms:
        print(f"      best cell top-mass = {tms[-1][0]:.5f} at (s_P,s_Q)={tms[-1][1]}")
        print(f"      worst cell top-mass = {tms[0][0]:.5f}   "
              f"(global {max(gl.values())/M:.5f}); concentration => {'YES' if tms[-1][0] > 0.05 else 'no'}")


if __name__ == "__main__":
    main()
