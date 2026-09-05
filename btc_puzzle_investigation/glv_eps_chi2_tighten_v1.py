#!/usr/bin/env python3
"""
glv_eps_chi2_tighten_v1.py

Take the ONE orbit-invariant candidate to its logical conclusion: is eps(d)
(core/flap of x([d]G)) predicted by chi2(d) (QR-ness of the scalar mod n)?
chi2 is the sole GLV-orbit-invariant scalar label on secp (glv_eps_scalar_...v1),
and ALSO +-d-invariant (chi2(-1)=1 since n=1 mod 4), so both eps and chi2 descend
to the (n-1)/6 mu6-orbit space. Closure theorem => MI(eps;chi2)=O(p^-1/2) (~2^-128
at secp) given Lemma W. Here: push N to ~300k empirically, confirm z stays flat and
MI~1/N (noise-scaling), and eyeball the exact eps x chi2 table.

Method note (scope): [k]G built by consecutive addition for k=1..N (fast) -> scalars
are CONSECUTIVE, not random; chi2 over consecutive ints is a representative
character sample, and the matched shuffle control absorbs the walk's serial
correlation in eps. A random-d cross-check (slower, smaller N) is in the companion
glv_eps_scalar_multiplicative_v1 (N=12k, also null).
Exact integers in the eps/chi2 path; float only in MI vs matched null.
"""
import math, random
from collections import Counter
from ecc_secp256k1 import scalar_mul, N_ORDER, P as P_CURVE
from glv_fundamental_domain_law_v1 import make_lift, cube_roots, AP_SECP, BP_SECP
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce

n = N_ORDER; p = P_CURVE


def om2(w):
    u, v = w
    return (v - u, -u)


def add_affine(P1, P2):
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


def mi_bits(fs, ts, nf, nt):
    J = [[0] * nt for _ in range(nf)]
    for a, b in zip(fs, ts): J[a][b] += 1
    tot = len(fs)
    rs = [sum(r) for r in J]; cs = [sum(J[i][j] for i in range(nf)) for j in range(nt)]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
               for i in range(nf) for j in range(nt) if J[i][j] and rs[i] and cs[j])


def main():
    R1, R2 = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    R1, R2, DET, reduce_P, eis = make_lift(P_CURVE, R1, R2)
    b1, b2 = cube_roots(p)
    beta = b1 if eis((b1 * 12345) % p) == reduce_P(*om2(eis(12345))) else b2
    R1t, R2t = tuple(R1), tuple(R2)

    def eps_of_x(x):
        U0 = eis(x); U1 = eis((beta * x) % p)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0): return 1
        if c == R1t or c == R2t: return 2
        if c == (-R1t[0], -R1t[1]) or c == (-R2t[0], -R2t[1]): return 0
        return 3

    e2 = (n - 1) // 2
    print(f"chi2(-1) = {'+1 (chi2 is +-d invariant)' if pow(n-1, e2, n) == 1 else '-1'}")

    N = 300000
    G = scalar_mul(1)
    E = []; C = []
    cur = G
    for k in range(1, N + 1):
        E.append(eps_of_x(cur[0]))
        C.append(1 if pow(k, e2, n) == 1 else 0)   # chi2(k)
        cur = add_affine(cur, G)
        if cur is None: cur = G
    M = len(E)
    mc = Counter(E); qr = sum(C) / M
    print(f"M={M}  eps marginal 0:{mc[0]/M:.3f} core:{mc[1]/M:.3f} +:{mc[2]/M:.3f} oth:{mc[3]/M:.4f}"
          f"  chi2=QR frac {qr:.3f}")

    # exact eps x chi2 table (proportions)
    J = [[0, 0] for _ in range(4)]
    for e, c in zip(E, C): J[e][c] += 1
    print("  eps x chi2 counts (rows eps=-/core/+/oth, cols chi2=nonQR/QR):")
    for e in range(4):
        tot = sum(J[e]) or 1
        print(f"    eps={e}: {J[e]}  (P(QR|eps)={J[e][1]/tot:.4f})")

    print("\n  MI(eps; chi2) scaling + shuffle control:")
    rng = random.Random(7)
    for NN in [50000, 100000, 200000, 300000]:
        obs = mi_bits(E[:NN], C[:NN], 4, 2)
        nulls = [mi_bits(E[:NN], random.sample(C[:NN], NN), 4, 2) for _ in range(150)]
        mu = sum(nulls) / len(nulls); sd = (sum((q - mu) ** 2 for q in nulls) / len(nulls)) ** 0.5
        z = (obs - mu) / sd if sd else 0.0
        print(f"    N={NN:6d}: MI={obs:.6f} null={mu:.6f} z={z:+6.2f}")
    ct = C[:]; rng.shuffle(ct)
    cobs = mi_bits(E, ct, 4, 2)
    cn = [mi_bits(E, random.sample(ct, M), 4, 2) for _ in range(150)]
    cmu = sum(cn) / len(cn); csd = (sum((q - cmu) ** 2 for q in cn) / len(cn)) ** 0.5
    print(f"    CONTROL (shuffled chi2) z = {(cobs-cmu)/csd if csd else 0:+.2f}")
    print("\n  Reading: MI~1/N + z flat = null consistent with closure O(p^-1/2)")
    print("  (~2^-128 at secp). Growing z + clean control = eps predicts chi2 (would")
    print("  contradict closure / reveal Lemma W wrong). Report facts, scope to N/consecutive.")


if __name__ == "__main__":
    main()
