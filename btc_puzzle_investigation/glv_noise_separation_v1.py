#!/usr/bin/env python3
"""
glv_noise_separation_v1.py

Wheat-from-chaff: separate a real (tiny) signal from sampling noise using the
SCALING DISCRIMINATOR (a real effect's z grows ~sqrt(N); noise stays flat / MI~1/N).
Aimed at the two places a leak could hide:

 (A) the lambda2 transition-memory excess (REAL vs control), z vs N.  If the +G
     step leaves a fingerprint, (lambda2_REAL - lambda2_CTRL)/sd grows with N.

 (B) the two-point additive correction V = eis(x(P+Q)) - folded(eis(x_P)+eis(x_Q)).
     V is a function of THREE coordinates, so it is OUTSIDE the single-sum closure
     theorem (the named bilinear gap) -- the one curve-side place a leak is not yet
     ruled out.  We ask, with scaling + matched control, whether a bounded
     projection of V (sextant / norm-bucket) carries the SCALAR relationship of the
     pair: a%m (single), (a+b)%m and (a-b)%m (the joint scalar the group law mixes).

Exact integers in the lift/V/state path (p=100003, full group precomputed);
float only in the eigenvalue / MI rank statistic vs a matched null.

VERDICT rule (printed): SIGNAL = MI>>null AND z grows ~sqrt(N) AND control~0.
Otherwise NOISE/chaff at this readout & N.
"""
import math, random
from collections import Counter, defaultdict
import numpy as np
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv, enorm

P = 100003


def add_curve(P1, P2, p=P):
    if P1 is None: return P2
    if P2 is None: return P1
    x1, y1 = P1; x2, y2 = P2
    if x1 == x2:
        if (y1 + y2) % p == 0: return None
        lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def find_gen(p=P):
    for x in range(1, p):
        rhs = (x * x * x + 7) % p
        if pow(rhs, (p - 1) // 2, p) == 1:
            y = sqrt_mod(rhs, p)
            if y: return (x, int(y))
    return None


R1, R2 = reduced_basis(P)
DET = R1[0] * R2[1] - R1[1] * R2[0]


def eis(X):
    c1 = rdiv(X * R2[1], DET); c2 = rdiv(-X * R1[1], DET)
    return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))


def sextant(u, v):
    if u == 0 and v == 0: return 0
    for k in range(6):
        if v >= 0 and (u - v) >= 0 and u > 0: return k
        u, v = v, v - u
    return 0 if v >= 0 else 3


def fold(sx, sy):
    c1 = rdiv(sx * R2[1] - sy * R2[0], DET)
    c2 = rdiv(-sx * R1[1] + sy * R1[0], DET)
    return (sx - (c1 * R1[0] + c2 * R2[0]), sy - (c1 * R1[1] + c2 * R2[1])), (c1, c2)


def mi_bits(fs, ts, nf, nt):
    J = [[0] * nt for _ in range(nf)]
    for a, b in zip(fs, ts): J[a][b] += 1
    tot = len(fs)
    rs = [sum(r) for r in J]; cs = [sum(J[i][j] for i in range(nf)) for j in range(nt)]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
               for i in range(nf) for j in range(nt) if J[i][j] and rs[i] and cs[j])


def lam2_of(state_seq):
    idx = {s: i for i, s in enumerate(sorted(set(state_seq)))}
    m = len(idx); C = np.zeros((m, m))
    for a, b in zip(state_seq[:-1], state_seq[1:]): C[idx[a], idx[b]] += 1
    rows = C.sum(1, keepdims=True)
    T = np.divide(C, rows, out=np.zeros_like(C), where=rows > 0)
    ev = sorted((abs(e) for e in np.linalg.eigvals(T)), reverse=True)
    return ev[1] if len(ev) > 1 else 0.0


def main():
    G = find_gen()
    # precompute affine multiples  pts[k] = [k]G for k=1..n  (stop before O)
    pts = [None, G]; cur = G
    while True:
        cur = add_curve(cur, G)
        if cur is None: break          # reached O = [ord]G
        pts.append(cur)
    n = len(pts) - 1                   # pts[1..n] are the affine points
    zx = [None] + [eis(pts[k][0]) for k in range(1, n + 1)]  # lift of x([k]G)
    print(f"=== p={P}, affine multiples n={n}, generator {G} ===\n")

    # ---------- (A) lambda2 excess vs N ----------
    print("(A) transition-memory lambda2: REAL (consecutive kG) vs control, z vs N")
    rng = random.Random(1)
    print(f"    {'N':>7} {'lam2_REAL':>10} {'ctrl_mean':>10} {'ctrl_sd':>9} {'z':>7}")
    zs_A = []
    for N in [5000, 10000, 20000, 40000]:
        real = [fold(zx[k][0] + zx[k + 1][0], zx[k][1] + zx[k + 1][1])[1]
                for k in range(1, N + 1)]
        l2_real = lam2_of(real)
        ctrls = []
        for _ in range(40):
            ids = [rng.randrange(1, n + 1) for _ in range(N + 1)]
            st = [fold(zx[ids[k]][0] + zx[ids[k + 1]][0],
                       zx[ids[k]][1] + zx[ids[k + 1]][1])[1] for k in range(N)]
            ctrls.append(lam2_of(st))
        mu = np.mean(ctrls); sd = np.std(ctrls)
        z = (l2_real - mu) / sd if sd else 0.0
        zs_A.append(z)
        print(f"    {N:>7} {l2_real:>10.4f} {mu:>10.4f} {sd:>9.4f} {z:>+7.2f}")
    growth = "GROWS (candidate signal)" if zs_A[-1] > 2 and zs_A[-1] > zs_A[0] + 1 else \
             "FLAT (noise: +G leaves no transition fingerprint)"
    print(f"    verdict: z-trajectory {['%+.1f'%z for z in zs_A]} => {growth}\n")

    # ---------- (B) V two-point leak, scaling + control ----------
    print("(B) two-point correction V leak (closure-uncovered): proj(V) vs scalar rel.")
    M = 40000
    rng2 = random.Random(7)
    sV = []; nV = []; A = []; Bb = []
    for _ in range(M):
        a = rng2.randrange(1, n + 1); b = rng2.randrange(1, n + 1)
        Psum = add_curve(pts[a], pts[b])
        if Psum is None: continue
        (fx, fy), _ = fold(zx[a][0] + zx[b][0], zx[a][1] + zx[b][1])
        z3 = eis(Psum[0])
        V = (z3[0] - fx, z3[1] - fy)
        sV.append(sextant(*V))
        s = enorm(V)
        nV.append(0 if s < P // 6 else (1 if s < P // 3 else 2))
        A.append(a); Bb.append(b)
    M = len(sV)

    def scale_test(name, feat, nf, tgt, nt):
        rng3 = random.Random(hash(name) & 0xffff)
        zs = []
        for N in [M // 4, M // 2, M]:
            f = feat[:N]; t = tgt[:N]
            obs = mi_bits(f, t, nf, nt)
            nulls = [mi_bits(f, random.sample(t, len(t)), nf, nt) for _ in range(120)]
            mu = np.mean(nulls); sd = np.std(nulls)
            zs.append((obs - mu) / sd if sd else 0.0)
        ct = tgt[:]; rng3.shuffle(ct)
        cobs = mi_bits(feat, ct, nf, nt)
        cn = [mi_bits(feat, random.sample(ct, len(ct)), nf, nt) for _ in range(120)]
        cz = (cobs - np.mean(cn)) / (np.std(cn) or 1)
        verd = "SIGNAL?" if zs[-1] > 3 and zs[-1] > zs[0] + 1 and abs(cz) < 2 else "noise"
        print(f"    {name:34s} z@N/4,N/2,N = {zs[0]:+5.1f},{zs[1]:+5.1f},{zs[2]:+5.1f}"
              f"  ctrl={cz:+4.1f}  => {verd}")

    tgts = {"a%6": [x % 6 for x in A], "(a+b)%6": [(a + b) % 6 for a, b in zip(A, Bb)],
            "(a-b)%6": [(a - b) % 6 for a, b in zip(A, Bb)]}
    print(f"    (M={M} random independent pairs)")
    for tn, tv in tgts.items():
        scale_test(f"sextant(V) vs {tn}", sV, 6, tv, 6)
    for tn, tv in tgts.items():
        scale_test(f"normbucket(V) vs {tn}", nV, 3, tv, 6)
    print("\n  SIGNAL needs z growing past 3 AND control~0. Flat/declining = chaff at")
    print("  this readout. V is the closure's bilinear gap -- the live place to probe.")


if __name__ == "__main__":
    main()
