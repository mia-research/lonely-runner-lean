#!/usr/bin/env python3
"""
glv_lambda2_investigate_v4.py

CAREFUL redo of the lambda2-gap investigation. v2/v3 built control chains with
INDEX arithmetic (j+=h; if j>n: j-=n) that wrapped at n (affine count) instead of
the true group order n+1, and mishandled O -- so REAL(G) (N<n, never wraps) was
clean but every control was noise-inflated by a wrap defect. That bug could bury a
real G-signal. Here every chain is a DIRECT POINT-WALK (S, S+H, S+2H, ... via point
addition: no index wrap, O handled), so REAL and controls are on equal footing.

Questions (investigate, don't dismiss):
  (1) group order -- prime? (if composite, small-order steps => periodic chains => tail)
  (2) gap(H) = lambda2(walk by step H) - iid_mean, for H = G and many steps H=[h]G.
      Restrict controls to FULL-ORDER generators (gcd(h,ord)=1) for apples-to-apples.
  (3) where does G fall in the CLEAN generator-gap distribution? bootstrap gap(G).
  (4) characterize the spread: does gap(H) track ord([h]G) / arithmetic of h?
Exact integers in lift/state path; float only in eigenvalues.
"""
import random
from math import gcd
import numpy as np
from sympy import factorint
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


def state_x(x1, x2):
    z1, z2 = eis(x1), eis(x2)
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


def walk_states(start_pt, H, N):
    """states of S, S+H, S+2H, ... by point addition (bug-free). O -> restart offset."""
    xs = []
    cur = start_pt
    steps = 0
    while len(xs) < N + 1 and steps < N + 5:
        steps += 1
        if cur is None:                    # hit O: skip it, continue the walk
            cur = add_curve(cur, H); continue
        xs.append(cur[0]); cur = add_curve(cur, H)
    return [state_x(xs[k], xs[k + 1]) for k in range(len(xs) - 1)]


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
    ordE = len(pts)                        # group order (affine + O)
    print(f"p={P}: group order = {ordE}, factor = {dict(factorint(ordE))}, "
          f"prime={len(factorint(ordE))==1}")

    N = 60000
    rng = random.Random(11)

    # iid baseline (independent random lifts)
    iid = []
    for _ in range(50):
        idxs = [rng.randrange(1, ordE) for _ in range(N + 1)]
        iid.append(lam2([state_x(pts[idxs[k]][0], pts[idxs[k + 1]][0]) for k in range(N)]))
    iid_mu = np.mean(iid)
    print(f"iid_mean(lambda2) = {iid_mu:.5f}  (sd {np.std(iid):.5f})\n")

    def gap(H, start):
        return lam2(walk_states(start, H, N)) - iid_mu

    # (3) bootstrap gap(G) over several starts
    gG = [gap(G, pts[rng.randrange(1, ordE)]) for _ in range(8)]
    print(f"gap(G) over 8 starts: mean={np.mean(gG):+.5f} sd={np.std(gG):.5f}  "
          f"values={[f'{g:+.4f}' for g in gG]}")

    # (2)+(4) distribution over steps, split by full-order (coprime) vs not
    rows = []
    for _ in range(60):
        h = rng.randrange(2, ordE)
        H = pts[h]
        g = gap(H, pts[rng.randrange(1, ordE)])
        ordH = ordE // gcd(h, ordE)
        rows.append((h, gcd(h, ordE), ordH, g))
    copr = [g for (h, gc, oH, g) in rows if gc == 1]
    noncopr = [(oH, g) for (h, gc, oH, g) in rows if gc > 1]
    print(f"\nFULL-ORDER generator steps (gcd=1), n={len(copr)}:")
    print(f"  gap mean={np.mean(copr):+.5f} sd={np.std(copr):.5f} "
          f"min={np.min(copr):+.5f} max={np.max(copr):+.5f}")
    zG = (np.mean(gG) - np.mean(copr)) / (np.std(copr) or 1)
    below = sum(1 for g in copr if g < np.mean(gG))
    print(f"  gap(G)={np.mean(gG):+.5f} => percentile {below}/{len(copr)}  z={zG:+.2f}")
    if noncopr:
        print(f"\nnon-full-order steps (gcd>1), n={len(noncopr)}  (expect big gaps = periodic):")
        for oH, g in sorted(noncopr)[:6]:
            print(f"  ord([h]G)={oH:>7}: gap={g:+.5f}")
    print("\n  READ: if gap(G) is a typical draw among FULL-ORDER generators (|z|<2),")
    print("  the memory is generic to any generator's orbit; if G is an outlier, chase it.")
    print("  The tail (if any) should be the gcd>1 / small-order steps (periodic chains).")


if __name__ == "__main__":
    main()
