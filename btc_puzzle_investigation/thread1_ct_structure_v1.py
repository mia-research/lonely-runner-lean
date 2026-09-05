#!/usr/bin/env python3
"""
THREAD 1: finer structure of the addition-rounding transition operator C_T (beyond
lambda2). Does T reveal geometric/CM symmetry, and is the generator G special in any
ENTRY (not just lambda2, where v4 found G typical)?

(a) exact full-group transition matrix T for the consecutive-kG chain.
(b) central symmetry sigma:(c1,c2)->(-c1,-c2): does T[sigma i][sigma j]=T[i][j]?
(c) per-entry: G's T[i][j] vs distribution over random-generator chains -> z/entry.
Reveals real structure (symmetry) + any per-entry G fingerprint. p=100003, exact
counts; float only in eigen/z stats.
"""
import random
import numpy as np
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv

P = 100003
R1, R2 = reduced_basis(P); DET = R1[0] * R2[1] - R1[1] * R2[0]
STATES = [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)]
IDX = {s: i for i, s in enumerate(STATES)}


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


def state_of(z1, z2):
    sx, sy = z1[0] + z2[0], z1[1] + z2[1]
    c1 = rdiv(sx * R2[1] - sy * R2[0], DET); c2 = rdiv(-sx * R1[1] + sy * R1[0], DET)
    return (c1, c2)


def Tmatrix(states):
    C = np.zeros((9, 9))
    for a, b in zip(states[:-1], states[1:]):
        if a in IDX and b in IDX: C[IDX[a], IDX[b]] += 1
    rows = C.sum(1, keepdims=True)
    return np.divide(C, rows, out=np.zeros_like(C), where=rows > 0), C


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
    zx = [None] + [eis(pts[k][0]) for k in range(1, n + 1)]
    Gstates = [state_of(zx[k], zx[k + 1]) for k in range(1, n)]
    T, _ = Tmatrix(Gstates)

    print("THREAD 1: C_T transition structure (p=%d, full-group G-orbit)\n" % P)
    print("(a) transition matrix T (rows/cols = 9 states, order %s):" % STATES)
    for i in range(9):
        print("   ", " ".join(f"{T[i,j]:.3f}" for j in range(9)))

    # (b) central symmetry sigma:(c1,c2)->(-c1,-c2)
    sig = {i: IDX[(-s[0], -s[1])] for i, s in enumerate(STATES)}
    dev = max(abs(T[i, j] - T[sig[i], sig[j]]) for i in range(9) for j in range(9))
    print(f"\n(b) central symmetry T[i,j]=T[-i,-j]: max deviation = {dev:.4f} "
          f"({'HOLDS (T is centrally symmetric)' if dev < 0.01 else 'broken'})")
    # sextant-rotation symmetry rho:(c1,c2)-> rotate? test the 120deg lattice rotation om2 on states
    ev = sorted(((abs(e), e) for e in np.linalg.eigvals(T)), reverse=True)
    print(f"    eigenvalues |.|: {[f'{a:.3f}' for a,_ in ev[:4]]}")

    # (c) per-entry: G vs random-generator distribution
    rng = random.Random(5)
    NREP = 40
    ent = {(i, j): [] for i in range(9) for j in range(9)}
    NW = 40000
    for _ in range(NREP):
        h = rng.randrange(2, n); start = rng.randrange(1, n)
        seq = []
        j = start
        for _ in range(NW + 1):
            seq.append(j); j = (j + h) % (n + 1)
            if j == 0: j = 1
        st = [state_of(zx[seq[t]], zx[seq[t + 1]]) for t in range(NW)]
        Th, _ = Tmatrix(st)
        for i in range(9):
            for jj in range(9):
                ent[(i, jj)].append(Th[i, jj])
    # G's T on a matched window (first NW) for fair comparison
    TgW, _ = Tmatrix(Gstates[:NW + 1])
    print("\n(c) per-entry: G's T[i,j] vs random-generator dist (|z|>3 = G-specific):")
    flagged = []
    for i in range(9):
        for jj in range(9):
            arr = ent[(i, jj)]
            mu = np.mean(arr); sd = np.std(arr)
            if sd > 1e-9:
                z = (TgW[i, jj] - mu) / sd
                if abs(z) > 3:
                    flagged.append((abs(z), STATES[i], STATES[jj], TgW[i, jj], mu, z))
    flagged.sort(reverse=True)
    if flagged:
        for az, si, sj, g, mu, z in flagged[:8]:
            print(f"    {si}->{sj}: G={g:.4f} rand={mu:.4f} z={z:+.2f}")
    else:
        print("    no entry with |z|>3 -- G's transition matrix is typical of a generic")
        print("    generator entry-by-entry (consistent with the lambda2 finding).")


if __name__ == "__main__":
    main()
