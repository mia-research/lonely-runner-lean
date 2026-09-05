#!/usr/bin/env python3
"""
THREAD 2: finer projections of the two-point correction V = eis(x(P+Q)) -
(eis x_P + eis x_Q), in the closure theorem's bilinear gap. The 6 coarse
projections (sextant, norm-bucket) were flat; push resolution: k x k grid cell of V
(k=8,16) and V's exact sextant-pair, vs the scalar relationship (a+b),(a-b) mod m.
Scaling discriminator (z ~ sqrt(N) if signal) + shuffle control. p=100003.
"""
import math, random
import numpy as np
from fractions import Fraction as Fr
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv, enorm

P = 100003
R1, R2 = reduced_basis(P); DET = R1[0] * R2[1] - R1[1] * R2[0]


def add_c(A, B, p=P):
    if A is None: return B
    if B is None: return A
    x1, y1 = A; x2, y2 = B
    if x1 == x2:
        if (y1 + y2) % p == 0: return None
        lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def eis(X):
    c1 = rdiv(X * R2[1], DET); c2 = rdiv(-X * R1[1], DET)
    return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))


def frac_cell(V, k):
    c1 = Fr(V[0] * R2[1] - V[1] * R2[0], DET); c2 = Fr(V[1] * R1[0] - V[0] * R1[1], DET)
    a = int((c1 - c1.__floor__()) * k) % k; b = int((c2 - c2.__floor__()) * k) % k
    return a * k + b


def mi(fs, ts, nf, nt):
    J = [[0] * nt for _ in range(nf)]
    for a, b in zip(fs, ts): J[a][b] += 1
    tot = len(fs); rs = [sum(r) for r in J]; cs = [sum(J[i][j] for i in range(nf)) for j in range(nt)]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
               for i in range(nf) for j in range(nt) if J[i][j] and rs[i] and cs[j])


def main():
    G = None
    for x in range(1, P):
        if pow((x * x * x + 7) % P, (P - 1) // 2, P) == 1:
            y = sqrt_mod((x * x * x + 7) % P, P)
            if y: G = (x, int(y)); break
    pts = [None, G]; cur = G
    while True:
        cur = add_c(cur, G)
        if cur is None: break
        pts.append(cur)
    n = len(pts) - 1
    U = [None] + [eis(pts[k][0]) for k in range(1, n + 1)]

    rng = random.Random(11)
    M = 60000
    Vc = {8: [], 16: []}; AB = []; AmB = []
    for _ in range(M):
        a = rng.randrange(1, n + 1); b = rng.randrange(1, n + 1)
        Ps = add_c(pts[a], pts[b])
        if Ps is None: continue
        Us = eis(Ps[0])
        V = (Us[0] - U[a][0] - U[b][0], Us[1] - U[a][1] - U[b][1])
        Vc[8].append(frac_cell(V, 8)); Vc[16].append(frac_cell(V, 16))
        AB.append((a + b) % 6); AmB.append((a - b) % 6)
    M = len(AB)
    print(f"THREAD 2: finer V projections (p={P}, M={M})\n")

    def scale(name, feat, nf, tgt, nt):
        rr = random.Random(hash(name) & 0xffff); zs = []
        for NN in [M // 3, 2 * M // 3, M]:
            obs = mi(feat[:NN], tgt[:NN], nf, nt)
            nulls = [mi(feat[:NN], random.sample(tgt[:NN], NN), nf, nt) for _ in range(80)]
            mu = np.mean(nulls); sd = np.std(nulls)
            zs.append((obs - mu) / sd if sd else 0.0)
        ct = tgt[:]; rr.shuffle(ct)
        cobs = mi(feat, ct, nf, nt); cn = [mi(feat, random.sample(ct, M), nf, nt) for _ in range(80)]
        cz = (cobs - np.mean(cn)) / (np.std(cn) or 1)
        print(f"  {name:28s} z@N/3,2N/3,N={zs[0]:+5.1f},{zs[1]:+5.1f},{zs[2]:+5.1f} ctrl={cz:+4.1f}")

    for k in (8, 16):
        scale(f"V cell(k={k}) vs (a+b)%6", Vc[k], k * k, AB, 6)
        scale(f"V cell(k={k}) vs (a-b)%6", Vc[k], k * k, AmB, 6)
    print("\n  (finer grid than the 6 coarse projections; signal = z grows past 3 + ctrl~0)")


if __name__ == "__main__":
    main()
