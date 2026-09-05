#!/usr/bin/env python3
"""
Curve structure: is the addition-rounding transition operator C_T a TENSOR SQUARE
C_T = C_1 (x) C_1 ?  The stationary law is (3/4:1/8:1/8)^{(x)2} (tensor square); if
the two lift basis-coordinates c1,c2 evolve as INDEPENDENT 3-state Markov chains,
then C_T factors and its 9 eigenvalues = pairwise products of C_1's 3 eigenvalues.
This is the operator-level version of the tensor law and pins the {1,1/3,1/3,1/8,..}
spectrum. Pure lift geometry (p=100003, full G-orbit), exact counts; float in eig only.
"""
import numpy as np
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv

P = 100003
R1, R2 = reduced_basis(P); DET = R1[0] * R2[1] - R1[1] * R2[0]
S9 = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)]
I9 = {s: i for i, s in enumerate(S9)}
C3 = [-1, 0, 1]; I3 = {c: i for i, c in enumerate(C3)}


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


def state(z1, z2):
    sx, sy = z1[0] + z2[0], z1[1] + z2[1]
    c1 = rdiv(sx * R2[1] - sy * R2[0], DET); c2 = rdiv(-sx * R1[1] + sy * R1[0], DET)
    return (c1, c2)


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
    seq = [state(zx[k], zx[k + 1]) for k in range(1, n)]

    # joint 9x9 counts
    Cj = np.zeros((9, 9))
    for a, b in zip(seq[:-1], seq[1:]):
        if a in I9 and b in I9: Cj[I9[a], I9[b]] += 1
    Tj = Cj / Cj.sum(1, keepdims=True)

    # per-coordinate 3x3 transitions (marginal c1->c1', c2->c2')
    C1 = np.zeros((3, 3)); C2 = np.zeros((3, 3))
    for a, b in zip(seq[:-1], seq[1:]):
        C1[I3[a[0]], I3[b[0]]] += 1
        C2[I3[a[1]], I3[b[1]]] += 1
    T1 = C1 / C1.sum(1, keepdims=True)
    T2 = C2 / C2.sum(1, keepdims=True)

    print("C_1 (per-coordinate c1 transition, 3x3):")
    for i in range(3): print("   ", " ".join(f"{T1[i,j]:.4f}" for j in range(3)))
    print("C_2 (per-coordinate c2 transition):")
    for i in range(3): print("   ", " ".join(f"{T2[i,j]:.4f}" for j in range(3)))
    print(f"  C_1 == C_2 ? max|diff| = {np.max(np.abs(T1-T2)):.4f}")

    # factorization test: Tj[(i,j),(k,l)] =? T1[i,k]*T2[j,l]
    Tf = np.zeros((9, 9))
    for si, (i, j) in enumerate(S9):
        for sk, (k, l) in enumerate(S9):
            Tf[si, sk] = T1[I3[i], I3[k]] * T2[I3[j], I3[l]]
    dev = np.max(np.abs(Tj - Tf))
    print(f"\nTENSOR FACTORIZATION  C_T =? C_1 (x) C_2 :  max|C_T - C_1(x)C_2| = {dev:.4f}")
    print(f"  => {'C_T IS a tensor product (coordinates evolve independently)' if dev<0.02 else 'NOT a clean tensor product (dev %.3f)'%dev}")

    e1 = sorted((abs(e) for e in np.linalg.eigvals(T1)), reverse=True)
    ej = sorted((abs(e) for e in np.linalg.eigvals(Tj)), reverse=True)
    prod = sorted((a * b for a in e1 for b in e1), reverse=True)
    print(f"\n  C_1 eigenvalues |.|: {[f'{a:.4f}' for a in e1]}")
    print(f"  C_T eigenvalues |.|: {[f'{a:.4f}' for a in ej]}")
    print(f"  pairwise products of C_1 eigs: {[f'{a:.4f}' for a in prod]}")
    print(f"  spectrum match (C_T == C_1 eigs (x) C_1 eigs)? max|diff|="
          f"{max(abs(a-b) for a,b in zip(ej,prod)):.4f}")


if __name__ == "__main__":
    main()
