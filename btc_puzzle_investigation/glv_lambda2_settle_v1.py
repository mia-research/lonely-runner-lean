#!/usr/bin/env python3
"""
glv_lambda2_settle_v1.py

Settle the lambda2 transition-memory excess: is the +G step a real fingerprint or
finite-N convergence noise?  Push N to 160k with 60 control chains; a real effect's
|z| climbs past ~3 and grows ~sqrt(N).  Noise: REAL converges to the control band.
"""
import random
import numpy as np
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv

P = 100003
R1, R2 = reduced_basis(P)
DET = R1[0] * R2[1] - R1[1] * R2[0]


def add_curve(A, B, p=P):
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


def fold_state(sx, sy):
    c1 = rdiv(sx * R2[1] - sy * R2[0], DET)
    c2 = rdiv(-sx * R1[1] + sy * R1[0], DET)
    return (c1, c2)


def lam2(seq):
    idx = {s: i for i, s in enumerate(sorted(set(seq)))}
    m = len(idx); C = np.zeros((m, m))
    for a, b in zip(seq[:-1], seq[1:]): C[idx[a], idx[b]] += 1
    rows = C.sum(1, keepdims=True)
    T = np.divide(C, rows, out=np.zeros_like(C), where=rows > 0)
    ev = sorted((abs(e) for e in np.linalg.eigvals(T)), reverse=True)
    return ev[1] if len(ev) > 1 else 0.0


def main():
    G = None
    for x in range(1, P):
        rhs = (x * x * x + 7) % P
        if pow(rhs, (P - 1) // 2, P) == 1:
            y = sqrt_mod(rhs, P)
            if y: G = (x, int(y)); break
    pts = [None, G]; cur = G
    while True:
        cur = add_curve(cur, G)
        if cur is None: break
        pts.append(cur)
    n = len(pts) - 1
    zx = [None] + [eis(pts[k][0]) for k in range(1, n + 1)]
    print(f"p={P}, n={n}\n  {'N':>7} {'lam2_REAL':>10} {'ctrl_mean':>10} {'ctrl_sd':>9} {'z':>7}")
    rng = random.Random(2)
    traj = []
    for N in [20000, 40000, 80000, 160000]:
        real = [fold_state(zx[k][0] + zx[k + 1][0], zx[k][1] + zx[k + 1][1])
                for k in range(1, N + 1)]
        lr = lam2(real)
        ctrls = []
        for _ in range(60):
            ids = [rng.randrange(1, n + 1) for _ in range(N + 1)]
            st = [fold_state(zx[ids[k]][0] + zx[ids[k + 1]][0],
                             zx[ids[k]][1] + zx[ids[k + 1]][1]) for k in range(N)]
            ctrls.append(lam2(st))
        mu = np.mean(ctrls); sd = np.std(ctrls)
        z = (lr - mu) / sd if sd else 0.0
        traj.append(z)
        print(f"  {N:>7} {lr:>10.5f} {mu:>10.5f} {sd:>9.5f} {z:>+7.2f}")
    verdict = ("SIGNAL: |z| grows past 3" if abs(traj[-1]) > 3 and traj[-1] > traj[1]
               else "NOISE: no signal-scaling; +G leaves no transition fingerprint")
    print(f"\n  z-trajectory {['%+.1f'%z for z in traj]} => {verdict}")


if __name__ == "__main__":
    main()
