#!/usr/bin/env python3
"""
glv_lambda2_settle_v2.py

The lambda2 gap (REAL consecutive kG vs i.i.d. lifts) is a STABLE ~0.004, not
growing -- so z climbs only as the control sd shrinks.  Decisive question: is that
gap SPECIFIC to G (a scalar/curve fingerprint) or is it what ANY fixed-step
arithmetic progression gives (generic deterministic-walk correlation)?

Three chains, lambda2 at N up to 90k (n=99666):
  REAL      : step G           (P, P+G, P+2G, ...)
  CTRL-fixH : step H=[h]G, random h  (another arithmetic progression, different step)
  CTRL-iid  : independent random lifts (no sequence)
If REAL == CTRL-fixH != CTRL-iid  => the gap is a generic AP-correlation, NOT a
G-/scalar-specific fingerprint (chaff for leakage).  If REAL != CTRL-fixH => G-specific.
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

    def ap_chain(step_idx, N, start=1):
        """states of consecutive terms of the AP start, start+step, ... (indices mod n)."""
        seq = []
        j = start
        for _ in range(N + 1):
            seq.append(j)
            j = j + step_idx
            if j > n: j -= n
            if j < 1: j += n
        return [state(zx[seq[k]], zx[seq[k + 1]]) for k in range(N)]

    rng = random.Random(3)
    print(f"p={P}, n={n}\n  {'N':>6} | {'REAL(G)':>9} {'fixH':>9} {'iid_mean':>9} {'iid_sd':>8}"
          f" | {'gap_R':>7} {'gap_H':>7}")
    for N in [20000, 40000, 80000, 90000]:
        lR = lam2(ap_chain(1, N))
        h = rng.randrange(2, n)                 # random nonzero step != 1
        lH = lam2(ap_chain(h, N, start=rng.randrange(1, n)))
        iid = []
        for _ in range(50):
            ids = [rng.randrange(1, n + 1) for _ in range(N + 1)]
            iid.append(lam2([state(zx[ids[k]], zx[ids[k + 1]]) for k in range(N)]))
        mu = np.mean(iid); sd = np.std(iid)
        print(f"  {N:>6} | {lR:>9.5f} {lH:>9.5f} {mu:>9.5f} {sd:>8.5f} | "
              f"{lR-mu:>+7.4f} {lH-mu:>+7.4f}")
    print("\n  gap_R (REAL) vs gap_H (fixed random step): if gap_R ~ gap_H, the ~0.004")
    print("  excess is a GENERIC arithmetic-progression correlation, not a G-/scalar")
    print("  fingerprint. If gap_R >> gap_H ~ 0, it is specific to the generator G.")


if __name__ == "__main__":
    main()
