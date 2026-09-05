#!/usr/bin/env python3
"""
glv_lambda2_settle_v3.py

Decisive close on the lambda2 gap.  v2 compared step-G against ONE random step per
N (not apples-to-apples: G fixed, H varying).  v3 fixes N and builds the FULL
DISTRIBUTION of the lambda2 gap over many random steps H, then asks where step-G
(=consecutive multiples, gap_R) falls in it.

  gap(step) = lambda2( AP-lift-state-chain with that step ) - lambda2_mean(iid)

If gap_R is a TYPICAL draw from the gap_H distribution  => the ~0.0047 excess is a
generic "fixed-step orbit has more short-range lift-correlation than iid" effect,
depending on the step map, NOT special to G / not scalar info.
If gap_R is a strong OUTLIER (|percentile| extreme) => G-specific, worth chasing.
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


def state(z1, z2):
    sx, sy = z1[0] + z2[0], z1[1] + z2[1]
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
    N = 60000
    rng = random.Random(5)

    def ap_gap(step, start):
        seq = []; j = start
        for _ in range(N + 1):
            seq.append(j); j += step
            if j > n: j -= n
            if j < 1: j += n
        return lam2([state(zx[seq[k]], zx[seq[k + 1]]) for k in range(N)])

    # iid band
    iid = []
    for _ in range(50):
        ids = [rng.randrange(1, n + 1) for _ in range(N + 1)]
        iid.append(lam2([state(zx[ids[k]], zx[ids[k + 1]]) for k in range(N)]))
    iid_mu = np.mean(iid)

    lR = ap_gap(1, 1)                              # step G (consecutive)
    gap_R = lR - iid_mu
    # distribution over many random steps H (coprime-ish, any nonzero)
    steps = [rng.randrange(2, n) for _ in range(40)]
    gaps_H = [ap_gap(h, rng.randrange(1, n)) - iid_mu for h in steps]
    gaps_H = np.array(gaps_H)
    muH, sdH = gaps_H.mean(), gaps_H.std()
    below = int(np.sum(gaps_H < gap_R))
    print(f"p={P}, n={n}, N={N}, iid_mean(lambda2)={iid_mu:.5f}")
    print(f"  step-G gap_R                 = {gap_R:+.5f}")
    print(f"  random-step gaps_H: mean={muH:+.5f}  sd={sdH:.5f}  "
          f"min={gaps_H.min():+.5f} max={gaps_H.max():+.5f}")
    print(f"  gap_R percentile among H     = {below}/40  "
          f"(z vs H-dist = {(gap_R-muH)/sdH:+.2f})")
    print()
    if abs((gap_R - muH) / sdH) < 2:
        print("  => step-G is a TYPICAL fixed-step draw: the ~0.0047 excess is a GENERIC")
        print("     AP-orbit lift-correlation (fixed-step orbits carry more short-range")
        print("     memory than iid), NOT special to G, NOT scalar information. Chaff.")
    else:
        print("  => step-G is an OUTLIER vs random steps: G-specific fingerprint, chase it.")


if __name__ == "__main__":
    main()
