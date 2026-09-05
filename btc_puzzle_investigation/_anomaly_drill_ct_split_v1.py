#!/usr/bin/env python3
"""
ANOMALY DRILL #1 -- the C_T lifted degeneracy.

ANOMALY. The tensor-square law C_T = C_1 (x) C_1 predicts the 9 eigenvalues of C_T are the
pairwise products of C_1's {1, 1/3, 1/9}.  That spectrum contains an EXACTLY DEGENERATE PAIR
at 1/3, with eigenvectors  v (x) u  and  u (x) v   (u = stationary of C_1, v = its 1/3-vector).
Measurement (v1 master, Part IV): lambda_2 = 0.339, lambda_3 = 0.328.  The mean is 1/3 to 3
decimals; the DEGENERACY IS SPLIT by ~3%.

TASK. Characterize the splitting. NOT "is it big enough to matter" -- a lifted degeneracy is a
symmetry-breaking coupling and its SYMMETRY TYPE is the object, independent of its magnitude.
Report the magnitude; do not convert it into a verdict.

QUESTIONS (each has a definite answer):
 Q1. Is the degenerate-block trace preserved?  lambda_2 + lambda_3 =? 2/3.
 Q2. Is C_T symmetric under the coordinate swap S:(c1,c2)->(c2,c1)?  If yes, the eigenvectors
     are forced into swap-even / swap-odd channels and the splitting IS the even-odd gap.
 Q3. What is the SYMMETRY TYPE of the lambda_2 / lambda_3 eigenvectors under S?
 Q4. How does delta = lambda_2 - lambda_3 scale with p?  const => arithmetic coupling.
     -> 0  => finite-orbit artifact.  Fit the exponent, do not guess it.
 Q5. Does the swap-odd channel coincide with the mu_3 / mu_6 structure, or is it new?

FLOAT CARVE-OUT: transition counts are exact integers; float enters only in eig() of a 9x9
(an analytic size, no key in path). Same carve-out as ct_tensor_structure_v1.py.
"""
import numpy as np
from sympy import isprime
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv

S9 = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)]
I9 = {s: i for i, s in enumerate(S9)}
I3 = {-1: 0, 0: 1, 1: 2}

# swap permutation matrix on the 9 states: (c1,c2) -> (c2,c1)
SW = np.zeros((9, 9))
for i, (a, b) in enumerate(S9):
    SW[i, I9[(b, a)]] = 1.0


def build(p, gen_index=0):
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
        c1 = rdiv(sx * R2[1] - sy * R2[0], DET)
        c2 = rdiv(-sx * R1[1] + sy * R1[0], DET)
        return (c1, c2)

    # generator
    found = 0; G = None
    for x in range(1, p):
        r = (x * x * x + 7) % p
        if pow(r, (p - 1) // 2, p) == 1:
            y = sqrt_mod(r, p)
            if y:
                if found == gen_index: G = (x, int(y)); break
                found += 1
    pts = [None, G]; cur = G
    while True:
        cur = add_c(cur, G)
        if cur is None: break
        pts.append(cur)
    n = len(pts) - 1
    zx = [None] + [eis(pts[k][0]) for k in range(1, n + 1)]
    seq = [state(zx[k], zx[k + 1]) for k in range(1, n)]

    Cj = np.zeros((9, 9))
    C1 = np.zeros((3, 3)); C2 = np.zeros((3, 3))
    for a, b in zip(seq[:-1], seq[1:]):
        if a in I9 and b in I9: Cj[I9[a], I9[b]] += 1
        if a[0] in I3 and b[0] in I3: C1[I3[a[0]], I3[b[0]]] += 1
        if a[1] in I3 and b[1] in I3: C2[I3[a[1]], I3[b[1]]] += 1
    rs = Cj.sum(1, keepdims=True); rs[rs == 0] = 1
    Tj = Cj / rs
    T1 = C1 / C1.sum(1, keepdims=True)
    T2 = C2 / C2.sum(1, keepdims=True)
    return Tj, T1, T2, n


def analyze(p, gen_index=0):
    Tj, T1, T2, n = build(p, gen_index)
    w, V = np.linalg.eig(Tj)
    idx = np.argsort(-np.abs(w))
    w, V = w[idx], V[:, idx]
    l2, l3 = abs(w[1]), abs(w[2])
    # tensor factorization deviation
    Tf = np.zeros((9, 9))
    for si, (i, j) in enumerate(S9):
        for sk, (k, l) in enumerate(S9):
            Tf[si, sk] = T1[I3[i], I3[k]] * T2[I3[j], I3[l]]
    dev = np.max(np.abs(Tj - Tf))
    # Q2: swap symmetry of C_T
    swdev = np.max(np.abs(SW @ Tj @ SW - Tj))
    # Q3: symmetry type of the lambda_2/lambda_3 eigenvectors under swap
    types = []
    for k in (1, 2):
        v = np.real(V[:, k]); nv = np.linalg.norm(v)
        if nv < 1e-12: types.append(float('nan')); continue
        v = v / nv
        sv = SW @ v
        types.append(float(np.dot(v, sv)))   # +1 = swap-EVEN, -1 = swap-ODD
    return dict(p=p, n=n, l2=l2, l3=l3, delta=l2 - l3, mean=(l2 + l3) / 2,
                dev=dev, swdev=swdev, t2=types[0], t3=types[1],
                e1=sorted((abs(e) for e in np.linalg.eigvals(T1)), reverse=True))


if __name__ == "__main__":
    print("ANOMALY DRILL #1 -- C_T lifted degeneracy at 1/3\n")
    primes = [p for p in (1009, 2003, 5003, 10007, 20011, 50021, 100003, 200003) if isprime(p) and p % 3 == 1]
    print(f"{'p':>8} {'n':>8} {'lam2':>9} {'lam3':>9} {'delta':>10} {'mean':>9} {'mean-1/3':>10} "
          f"{'tensor dev':>11} {'swap dev':>9} {'<v2,Sv2>':>9} {'<v3,Sv3>':>9}")
    rows = []
    for p in primes:
        try:
            r = analyze(p)
        except Exception as ex:
            print(f"{p:>8}  ERROR {ex}"); continue
        rows.append(r)
        print(f"{r['p']:>8} {r['n']:>8} {r['l2']:>9.5f} {r['l3']:>9.5f} {r['delta']:>10.6f} "
              f"{r['mean']:>9.5f} {r['mean']-1/3:>+10.6f} {r['dev']:>11.5f} {r['swdev']:>9.5f} "
              f"{r['t2']:>9.4f} {r['t3']:>9.4f}")

    print("\n--- Q1: degenerate-block trace  lambda_2+lambda_3 =? 2/3 ---")
    for r in rows:
        print(f"  p={r['p']:>7}  l2+l3 = {r['l2']+r['l3']:.6f}   2/3 = {2/3:.6f}   "
              f"diff = {r['l2']+r['l3']-2/3:+.6f}")

    print("\n--- Q4: scaling of delta = lambda_2 - lambda_3 ---")
    if len(rows) >= 3:
        ps = np.array([r['p'] for r in rows], float)
        ds = np.array([abs(r['delta']) for r in rows], float)
        m = ds > 0
        if m.sum() >= 3:
            a, b = np.polyfit(np.log(ps[m]), np.log(ds[m]), 1)
            print(f"  fit  log|delta| = {a:.4f}*log p + {b:.4f}   =>  |delta| ~ p^({a:.4f})")
            print(f"  reference exponents:  -0.5 = 1/sqrt(p) finite-orbit noise ;  0.0 = constant coupling")
    print("\n--- Q3 legend: <v,Sv> = +1 swap-EVEN, -1 swap-ODD, 0 no definite type ---")
