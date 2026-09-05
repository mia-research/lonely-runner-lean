#!/usr/bin/env python3
"""
ANOMALY DRILL #1 (v2) -- the C_T lifted degeneracy, WITH A MATCHED NULL.

v1 of this drill had two defects: only 3 primes passed the p=1 mod 3 filter, and two of them
had tiny orbits (n=146, n=3353) where a 9x9 operator estimated from n samples is noise. The
p^(-0.36) fit was dominated by those. Fixed here:
  - prime-ORDER curves only, so the orbit is the full group (n ~ p)
  - a MATCHED SURROGATE null: a sequence whose coordinates evolve INDEPENDENTLY with exactly
    the measured marginals T1, T2 and the same length n. This is the precise null for the
    tensor-square hypothesis. If the coupling is finite-orbit estimation noise, the surrogate
    reproduces it. If real, real >> surrogate.
  - scaling measured against n (sample count), which is what estimation noise tracks.

Reports the MAGNITUDE and the SYMMETRY TYPE. Does not convert either into a verdict.
"""
import numpy as np
from sympy import isprime
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv

S9 = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)]
I9 = {s: i for i, s in enumerate(S9)}
I3 = {-1: 0, 0: 1, 1: 2}
C3 = [-1, 0, 1]
SW = np.zeros((9, 9))
for i, (a, b) in enumerate(S9):
    SW[i, I9[(b, a)]] = 1.0


def curve_order(p):
    c = 1
    for x in range(p):
        r = (x * x * x + 7) % p
        if r == 0: c += 1
        elif pow(r, (p - 1) // 2, p) == 1: c += 2
    return c


def seq_of(p):
    R1, R2 = reduced_basis(p)
    DET = R1[0] * R2[1] - R1[1] * R2[0]
    def add_c(A, B):
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
        return (rdiv(sx * R2[1] - sy * R2[0], DET), rdiv(-sx * R1[1] + sy * R1[0], DET))
    G = None
    for x in range(1, p):
        r = (x * x * x + 7) % p
        if pow(r, (p - 1) // 2, p) == 1:
            y = sqrt_mod(r, p)
            if y: G = (x, int(y)); break
    pts = [None, G]; cur = G
    while True:
        cur = add_c(cur, G)
        if cur is None: break
        pts.append(cur)
    n = len(pts) - 1
    zx = [None] + [eis(pts[k][0]) for k in range(1, n + 1)]
    return [state(zx[k], zx[k + 1]) for k in range(1, n)], n


def ops(seq):
    Cj = np.zeros((9, 9)); C1 = np.zeros((3, 3)); C2 = np.zeros((3, 3))
    for a, b in zip(seq[:-1], seq[1:]):
        if a in I9 and b in I9: Cj[I9[a], I9[b]] += 1
        if a[0] in I3 and b[0] in I3: C1[I3[a[0]], I3[b[0]]] += 1
        if a[1] in I3 and b[1] in I3: C2[I3[a[1]], I3[b[1]]] += 1
    rs = Cj.sum(1, keepdims=True); rs[rs == 0] = 1
    r1 = C1.sum(1, keepdims=True); r1[r1 == 0] = 1
    r2 = C2.sum(1, keepdims=True); r2[r2 == 0] = 1
    return Cj / rs, C1 / r1, C2 / r2


def metrics(Tj, T1, T2):
    Tf = np.zeros((9, 9))
    for si, (i, j) in enumerate(S9):
        for sk, (k, l) in enumerate(S9):
            Tf[si, sk] = T1[I3[i], I3[k]] * T2[I3[j], I3[l]]
    dev = float(np.max(np.abs(Tj - Tf)))
    w, V = np.linalg.eig(Tj)
    idx = np.argsort(-np.abs(w)); w, V = w[idx], V[:, idx]
    l2, l3 = abs(w[1]), abs(w[2])
    swdev = float(np.max(np.abs(SW @ Tj @ SW - Tj)))
    ts = []
    for k in (1, 2):
        v = np.real(V[:, k]); nv = np.linalg.norm(v)
        ts.append(float(np.dot(v / nv, SW @ (v / nv))) if nv > 1e-12 else float('nan'))
    return dev, l2, l3, swdev, ts


def surrogate(T1, T2, n, rng):
    """independent-coordinate sequence with EXACTLY the measured marginals -> the tensor null"""
    def walk(T):
        s = rng.integers(0, 3); out = [s]
        for _ in range(n - 1):
            s = rng.choice(3, p=T[s]); out.append(s)
        return out
    a = walk(T1); b = walk(T2)
    return [(C3[a[i]], C3[b[i]]) for i in range(n)]


if __name__ == "__main__":
    rng = np.random.default_rng(20260717)
    print("ANOMALY DRILL #1 v2 -- C_T lifted degeneracy at 1/3, vs matched independent-coordinate null\n")
    cands = [p for p in range(1000, 400000) if p % 3 == 1 and isprime(p)]
    chosen = []
    for p in cands:
        if len(chosen) >= 6: break
        if p < 5000 and len(chosen) > 1: continue
        if isprime(curve_order(p)):
            chosen.append(p)
        if chosen and chosen[-1] == p:
            pass
    # spread them out
    chosen = sorted(set(chosen))
    print(f"prime-order curves selected: {chosen}\n")
    print(f"{'p':>8} {'n':>8} {'dev_real':>9} {'dev_surr':>9} {'ratio':>7} | "
          f"{'d_real':>9} {'d_surr':>9} {'ratio':>7} | {'l2+l3':>8} {'-2/3':>9} | {'swdev':>8}")
    rows = []
    for p in chosen:
        seq, n = seq_of(p)
        Tj, T1, T2 = ops(seq)
        dev, l2, l3, swdev, ts = metrics(Tj, T1, T2)
        # matched null, averaged over 3 draws
        ds, dl = [], []
        for _ in range(3):
            sq = surrogate(T1, T2, len(seq), rng)
            Tjs, T1s, T2s = ops(sq)
            d2, m2, m3, _, _ = metrics(Tjs, T1s, T2s)
            ds.append(d2); dl.append(abs(m2 - m3))
        dev_s = float(np.mean(ds)); del_s = float(np.mean(dl))
        rows.append((p, n, dev, dev_s, abs(l2 - l3), del_s, l2 + l3, swdev, ts))
        print(f"{p:>8} {n:>8} {dev:>9.5f} {dev_s:>9.5f} {dev/dev_s:>7.2f} | "
              f"{abs(l2-l3):>9.5f} {del_s:>9.5f} {abs(l2-l3)/del_s:>7.2f} | "
              f"{l2+l3:>8.5f} {l2+l3-2/3:>+9.5f} | {swdev:>8.5f}")

    print("\n--- Q1: degenerate-block trace preserved?  lambda_2+lambda_3 -> 2/3 ---")
    for r in rows:
        print(f"  p={r[0]:>7} n={r[1]:>7}   l2+l3 = {r[6]:.6f}   diff from 2/3 = {r[6]-2/3:+.6f}")

    print("\n--- Q4: scaling of the tensor deviation vs the matched null ---")
    ns = np.array([r[1] for r in rows], float)
    dr = np.array([r[2] for r in rows], float)
    dsu = np.array([r[3] for r in rows], float)
    if len(rows) >= 3:
        ar, _ = np.polyfit(np.log(ns), np.log(dr), 1)
        as_, _ = np.polyfit(np.log(ns), np.log(dsu), 1)
        print(f"  dev_real ~ n^({ar:+.4f})     dev_surrogate ~ n^({as_:+.4f})")
        print(f"  (-0.5 = pure estimation noise; 0.0 = a constant coupling that survives n->inf)")
    print("\n--- Q3: swap symmetry type of the lambda_2/lambda_3 eigenvectors ---")
    for r in rows:
        print(f"  p={r[0]:>7}  <v2,Sv2>={r[8][0]:+.4f}  <v3,Sv3>={r[8][1]:+.4f}   "
              f"(+1 even, -1 odd, 0 none)   swap-asym of C_T = {r[7]:.5f}")
