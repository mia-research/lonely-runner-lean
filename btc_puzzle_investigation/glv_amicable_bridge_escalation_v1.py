#!/usr/bin/env python3
"""
glv_amicable_bridge_escalation_v1.py

Escalation of the amicable-bridge probe past the coarse 6-sextant (which vanished ~1/N):
finer readouts of v_n = eis_{pi_n}(d) (GLV coord of d in P_n) vs v_p = eis_{pi_p}(X) (lift of
X=x([d]G) in P_p), where a sqrt(p)-scaling relation would survive even if the angular marginal
does not.

Readouts:
  (1) k x k lattice-cell grid of each 2-D coordinate (k=4, 8), MI + matched shuffle null, at
      growing M (power scaling).
  (2) joint (sextant, norm-band) -- the norm axis carried the 2nd single-x bridge.
Sets: constructed_keys_fullrange (36k known-d, full-power known-generator) [256-bit subset];
      real-82 solved keys (underpowered, coarse only).
Controls: self-MI(cell_p;cell_p) must FIRE; decoy MI(cell_n(d);cell_n(shuffled)) must FLOOR.
Exact integer lift path; MI is a statistic ranked vs a matched permutation null.
"""
import csv
import math
import random
import numpy as np
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce, enorm

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
NN = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
AP, BP = 367917413016453100223835821029139468249, 303414439467246543595250775667605759171


def rdiv(nu, de):
    if de < 0:
        nu, de = -nu, -de
    q, r = divmod(nu, de)
    return q + 1 if 2 * r >= de else q


def make(basis):
    R1, R2 = basis
    DET = R1[0] * R2[1] - R1[1] * R2[0]

    def eis(a):
        c1 = rdiv(a * R2[1], DET); c2 = rdiv(-a * R1[1], DET)
        return (a - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))

    def cell(a, k):
        u, v = eis(a)
        cx = (k * (2 * (u * R2[1] - v * R2[0]) + DET)) // (2 * DET)
        cy = (k * (2 * (v * R1[0] - u * R1[1]) + DET)) // (2 * DET)
        return min(max(cx, 0), k - 1) * k + min(max(cy, 0), k - 1)

    def sext(a):
        u, v = eis(a)
        if u == 0 and v == 0:
            return 0
        for kk in range(6):
            if v >= 0 and (u - v) >= 0 and u > 0:
                return kk
            u, v = v, v - u
        return 0 if v >= 0 else 3
    return eis, cell, sext


def mi_bits(J):
    tot = sum(sum(r) for r in J)
    if not tot:
        return 0.0
    rs = [sum(r) for r in J]; cs = [sum(J[i][j] for i in range(len(J))) for j in range(len(J[0]))]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
               for i in range(len(J)) for j in range(len(J[0])) if J[i][j] and rs[i] and cs[j])


def mi_z(xs, ys, nx, ny, rng, B=100):
    J = [[0] * ny for _ in range(nx)]
    for a, b in zip(xs, ys):
        J[a][b] += 1
    obs = mi_bits(J)
    nulls = []
    for _ in range(B):
        yp = ys[:]; rng.shuffle(yp)
        Jn = [[0] * ny for _ in range(nx)]
        for a, b in zip(xs, yp):
            Jn[a][b] += 1
        nulls.append(mi_bits(Jn))
    mu = sum(nulls) / len(nulls); sd = (sum((v - mu)**2 for v in nulls) / len(nulls))**0.5
    return obs, mu, (obs - mu) / sd if sd else 0.0


def run_set(name, ds, Xs, coarse_only=False):
    eis_p, cell_p, sext_p = make(gauss_reduce((AP, BP), (-BP, AP - BP)))
    eis_n, cell_n, sext_n = make(gauss_reduce((AP - 1, BP), (-BP, (AP - 1) - BP)))
    rng = random.Random(2025)
    Cp8 = [cell_p(int(x), 8) for x in Xs]; Cn8 = [cell_n(int(d), 8) for d in ds]
    Cp4 = [cell_p(int(x), 4) for x in Xs]; Cn4 = [cell_n(int(d), 4) for d in ds]
    # joint (sextant,norm) 6*4=24 classes
    def nb(a, eis, mod):
        u, v = eis(a); return min((4 * enorm((u, v))) // mod, 3)
    fp = [sext_p(int(x)) * 4 + nb(int(x), eis_p, P) for x in Xs]
    fn = [sext_n(int(d)) * 4 + nb(int(d), eis_n, NN) for d in ds]
    M = len(Xs)
    print(f"\n=== {name}  (M={M}) ===")
    if coarse_only:
        o, m, z = mi_z([s // 4 for s in fn], [s // 4 for s in fp], 6, 6, rng, 200)
        print(f"  sextant_n vs sextant_p (6x6): MI={o:.4f} null={m:.4f} z={z:+.1f}  (underpowered)")
        return
    print(f"  {'readout':<22}{'M':>7}{'MI':>10}{'null':>10}{'z':>7}")
    for M2 in (M // 4, M // 2, M):
        o, m, z = mi_z(Cn4[:M2], Cp4[:M2], 16, 16, rng, 80)
        print(f"  {'4x4 cell (16x16)':<22}{M2:>7}{o:>10.4f}{m:>10.4f}{z:>+7.1f}")
    o, m, z = mi_z(Cn8, Cp8, 64, 64, rng, 60)
    print(f"  {'8x8 cell (64x64)':<22}{M:>7}{o:>10.4f}{m:>10.4f}{z:>+7.1f}")
    o, m, z = mi_z(fn, fp, 24, 24, rng, 120)
    print(f"  {'(sext,norm) 24x24':<22}{M:>7}{o:>10.4f}{m:>10.4f}{z:>+7.1f}")
    # controls
    o, _, _ = mi_z(Cp8, Cp8, 64, 64, rng, 5)
    sh = Cn8[:]; rng.shuffle(sh)
    od, md, zd = mi_z(Cn8, sh, 64, 64, rng, 60)
    print(f"  CONTROLS: self-MI(cell_p;cell_p)={o:.3f} (must fire); "
          f"decoy z={zd:+.1f} (must floor)")


def main():
    print("=" * 70)
    print("Amicable bridge ESCALATION: finer readouts of v_n(d) vs v_p(X), both sets")
    print("=" * 70)
    z = np.load("constructed_keys_fullrange_v1.npz", allow_pickle=True)
    d = z["d"]; X = z["X"]
    bits = np.array([int(v).bit_length() for v in d])
    mask = bits >= 250
    run_set("constructed 256-bit (known generator)", list(d[mask]), list(X[mask]))

    rd, rx = [], []
    with open("puzzles_verified.csv") as f:
        for row in csv.DictReader(f):
            rd.append(int(row["private_key"], 16)); rx.append(int(row["X"], 16))
    run_set("real-82 solved keys", rd, rx, coarse_only=True)


if __name__ == "__main__":
    main()
