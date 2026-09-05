#!/usr/bin/env python3
"""
glv_addition_eps_reprobe_v1.py

Settle the ONE non-flat reading from glv_addition_lift_conditioned_v1: the
eps-homomorphism (eps_P, eps_Q) -> eps_S under point addition showed z climbing
0.2 -> 0.7 -> 1.3 over N=12k..48k (MI still ~1/N).  Is that a faint real
dependence or small-sample?  Push N to ~180k with a finer scaling ladder: a real
effect climbs ~sqrt(N) and MI plateaus; noise stays z~O(1) and MI ~1/N.

eps in {0(core), +, -, other}.  Exact integers in point/lift/label path.
"""
import math
import random
from collections import Counter

from glv_fundamental_domain_law_v1 import (make_lift, cube_roots,
                                           P_SECP, AP_SECP, BP_SECP)
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce
from glv_three_point_lift_v1 import ec_add, rand_point


def om2(w):
    u, v = w
    return (v - u, -u)


def mi_bits(J):
    tot = sum(sum(r) for r in J)
    if not tot:
        return 0.0
    rs = [sum(r) for r in J]
    cs = [sum(J[i][j] for i in range(len(J))) for j in range(len(J[0]))]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
               for i in range(len(J)) for j in range(len(J[0]))
               if J[i][j] and rs[i] and cs[j])


def main():
    R1, R2 = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    R1, R2, DET, reduce_P, eis = make_lift(P_SECP, R1, R2)
    b1, b2 = cube_roots(P_SECP)
    beta = b1 if eis((b1 * 12345) % P_SECP) == reduce_P(*om2(eis(12345))) else b2
    R1t, R2t = tuple(R1), tuple(R2)

    def eps_of_x(x):
        U0 = eis(x); U1 = eis((beta * x) % P_SECP)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0):
            return 1
        if c == R1t or c == R2t:
            return 2
        if c == (-R1t[0], -R1t[1]) or c == (-R2t[0], -R2t[1]):
            return 0
        return 3

    print("=" * 70)
    print("eps-homomorphism re-probe: (eps_P, eps_Q) -> eps_S under P (+) Q")
    print("=" * 70)
    NMAX = 180000
    rng = random.Random(9091)
    pairs = []   # ((eP,eQ), eS)
    while len(pairs) < NMAX:
        P1 = rand_point(P_SECP, rng); P2 = rand_point(P_SECP, rng)
        if P1[0] == P2[0]:
            continue
        S = ec_add(P1, P2, P_SECP)
        if S is None or 0 in (P1[0], P2[0], S[0]):
            continue
        eP, eQ, eS = eps_of_x(P1[0]), eps_of_x(P2[0]), eps_of_x(S[0])
        pairs.append(((eP, eQ), eS))
    M = len(pairs)
    mc = Counter(eS for _, eS in pairs)
    print(f"  M={M}   eps_S marginal 0-core:{mc[1]/M:.4f} +:{mc[2]/M:.4f} "
          f"-:{mc[0]/M:.4f} other:{mc[3]/M:.4f}\n")

    rr = random.Random(5)
    print("    N        MI        null       z      (real: z climbs ~sqrt(N), MI plateaus)")
    for NN in [30000, 60000, 120000, 180000]:
        sub = pairs[:NN]
        key = [k for k, _ in sub]; tgt = [t for _, t in sub]
        J = [[0] * 4 for _ in range(16)]
        for (a, b), c in zip(key, tgt):
            J[a * 4 + b][c] += 1
        obs = mi_bits(J)
        nulls = []
        for _ in range(200):
            sh = tgt[:]; rr.shuffle(sh)
            Jn = [[0] * 4 for _ in range(16)]
            for (a, b), c in zip(key, sh):
                Jn[a * 4 + b][c] += 1
            nulls.append(mi_bits(Jn))
        mu = sum(nulls) / len(nulls)
        sd = (sum((q - mu) ** 2 for q in nulls) / len(nulls)) ** 0.5
        z = (obs - mu) / sd if sd else 0.0
        print(f"  {NN:7d}  {obs:.6f}  {mu:.6f}  {z:+6.2f}")
    # control: shuffled pairing at full N
    key = [k for k, _ in pairs]; tgt = [t for _, t in pairs]
    ct = tgt[:]; rr.shuffle(ct)
    J = [[0] * 4 for _ in range(16)]
    for (a, b), c in zip(key, ct):
        J[a * 4 + b][c] += 1
    cobs = mi_bits(J)
    cn = []
    for _ in range(200):
        sh = ct[:]; rr.shuffle(sh)
        Jn = [[0] * 4 for _ in range(16)]
        for (a, b), c in zip(key, sh):
            Jn[a * 4 + b][c] += 1
        cn.append(mi_bits(Jn))
    cmu = sum(cn) / len(cn); csd = (sum((q - cmu) ** 2 for q in cn) / len(cn)) ** 0.5
    print(f"\n  CONTROL (shuffled) z at full N = {(cobs-cmu)/csd if csd else 0.0:+.2f}  (must be ~0)")


if __name__ == "__main__":
    main()
