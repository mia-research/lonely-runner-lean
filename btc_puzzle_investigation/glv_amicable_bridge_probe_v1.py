#!/usr/bin/env python3
"""
glv_amicable_bridge_probe_v1.py

Part B of the amicable bridge -- the colleague's exact question:
  does  d |-> X = x([d]G)  induce a relation between
    v_n = eis_{pi_n}(d)  -- d's GLV coordinate in P_n  (Babai reduce d vs the pi_n basis), and
    v_p = eis_{pi_p}(X)  -- X's lift coordinate in P_p ?
pi_n = pi_p - 1 (norm n), pi_p (norm p): concentric, coprime, theta-aligned rhombi.

We measure MI between coarse features of v_n and v_p at GROWING M, with a matched shuffle null
and a self-MI sanity control, and read the SCALING (signal: MI*M grows ~M / z ~ sqrt(M);
noise: MI*M ~ const / z ~ O(1)). Building the object honestly -- no verdict from one M.
Exact integer arithmetic in the point/lift path.
"""
import math
import random
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce, rdiv, sector_props
from fractions import Fraction as F

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
AP, BP = 367917413016453100223835821029139468249, 303414439467246543595250775667605759171
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8


def ec_add(Pa, Qa):
    if Pa is None:
        return Qa
    if Qa is None:
        return Pa
    x1, y1 = Pa; x2, y2 = Qa
    if x1 == x2 and (y1 + y2) % P == 0:
        return None
    m = ((3 * x1 * x1) % P * pow(2 * y1, P - 2, P) if Pa == Qa
         else (y2 - y1) % P * pow((x2 - x1) % P, P - 2, P)) % P
    x3 = (m * m - x1 - x2) % P
    return (x3, (m * (x1 - x3) - y1) % P)


def scalar_mul(k):
    R = None; Q = (GX, GY)
    while k:
        if k & 1:
            R = ec_add(R, Q)
        Q = ec_add(Q, Q)
        k >>= 1
    return R


def lifter(basis):
    R1, R2 = basis
    DET = R1[0] * R2[1] - R1[1] * R2[0]

    def eis(a):
        c1 = rdiv(a * R2[1], DET); c2 = rdiv(-a * R1[1], DET)
        return (a - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))
    return eis


def sextant(u, v):
    if u == 0 and v == 0:
        return 0
    for k in range(6):
        if v >= 0 and (u - v) >= 0 and u > 0:
            return k
        u, v = v, v - u
    return 0 if v >= 0 else 3


def mi_bits(J):
    tot = sum(sum(r) for r in J)
    if not tot:
        return 0.0
    rs = [sum(r) for r in J]; cs = [sum(J[i][j] for i in range(len(J))) for j in range(len(J[0]))]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
               for i in range(len(J)) for j in range(len(J[0])) if J[i][j] and rs[i] and cs[j])


def mi_pair(xs, ys, nx, ny):
    J = [[0] * ny for _ in range(nx)]
    for a, b in zip(xs, ys):
        J[a][b] += 1
    return mi_bits(J)


def main():
    print("=" * 70)
    print("Amicable bridge probe: v_n=eis_pi_n(d)  vs  v_p=eis_pi_p(x([d]G))")
    print("=" * 70)
    eis_p = lifter(gauss_reduce((AP, BP), (-BP, AP - BP)))
    eis_n = lifter(gauss_reduce((AP - 1, BP), (-BP, (AP - 1) - BP)))

    rng = random.Random(12345)
    Msmall, Mbig = 1500, 9000
    sp, sn, sn2 = [], [], []
    for _ in range(Mbig):
        d = rng.randrange(1, N)
        X = scalar_mul(d)[0]
        sp.append(sextant(*eis_p(X)))
        sn.append(sextant(*eis_n(d)))
        sn2.append(sextant(*eis_n(rng.randrange(1, N))))   # decoy d' (independent)

    print("\n  MI(sextant_n(d) ; sextant_p(X))  at growing M  [bits], with matched null z:")
    print(f"    {'M':>6} {'MI':>9} {'MI*M':>9} {'null':>9} {'z':>7}")
    for M in (Msmall, 3000, 4500, 6000, Mbig):
        obs = mi_pair(sn[:M], sp[:M], 6, 6)
        nulls = []
        for _ in range(150):
            yp = sp[:M]; rng.shuffle(yp)
            nulls.append(mi_pair(sn[:M], yp, 6, 6))
        mu = sum(nulls) / len(nulls); sd = (sum((v - mu)**2 for v in nulls)/len(nulls))**0.5
        z = (obs - mu) / sd if sd else 0
        print(f"    {M:>6} {obs:>9.5f} {obs*M:>9.1f} {mu:>9.5f} {z:>7.1f}")

    # controls
    self_mi = mi_pair(sp, sp, 6, 6)
    decoy_mi = mi_pair(sn, sn2, 6, 6)
    print(f"\n  controls: self-MI(sextant_p;sextant_p) = {self_mi:.4f} (must be large);")
    print(f"            decoy-MI(sextant_n(d);sextant_n(d')) = {decoy_mi:.5f} (must be ~0)")
    print("\n  Reading: MI*M ~ const (and z not growing with sqrt(M)) => v_n _|_ v_p at the")
    print("  coarse readout (per-point 2D-coordinate relation at the noise floor, scaling 1/N).")
    print("  MI*M growing / z ~ sqrt(M) => a real GLV-coord <-> lift-coord seam. NOTE: coarse")
    print("  sextant only; the full 2D coordinate + real-82/100k sets are the next escalation.")


if __name__ == "__main__":
    main()
