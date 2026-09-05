#!/usr/bin/env python3
"""
glv_eps_scalar_multiplicative_v1.py

Idea (user): the GLV-orbit label eps(d) in {0,+,-} (core/flap of x([d]G)) is a
MULTIPLICATIVE-side invariant. Does the INPUT scalar d's multiplicative structure
predict which orbits land core vs flap? Docs' "eps ⟂ chi6" was on OUTPUT coords;
this tests the SCALAR side.

Test the IDEA, not just the method:
  eps is GLV-orbit-invariant: eps(d)=eps(lam*d), lam^3=1 mod n. So eps can ONLY
  correlate with scalar labels that are THEMSELVES orbit-invariant; orbit-VARYING
  labels wash out. Whether chi_k(d) is invariant depends on chi_k(lam):
    secp n-1 = 2^6*3*... (v3=1): chi2 invariant; chi3, chi6, d%3, d%6 orbit-VARYING.
  So on secp the sharp candidate is chi2(d); the rest should wash out -- confirming
  THAT contrast is the real test of the mechanism.

Steps (secp, exact): (1) verify empirically which labels are GLV-invariant
(label(d)==label(lam*d) rate); (2) test MI(eps(d); label) with scaling + shuffle
control. A label with MI>>null AND z growing AND control~0 = eps predicts core/flap
from d's multiplicative structure.
"""
import math, random
from collections import Counter
from ecc_secp256k1 import scalar_mul, N_ORDER, P as P_CURVE
from glv_fundamental_domain_law_v1 import make_lift, cube_roots, P_SECP, AP_SECP, BP_SECP
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce

n = N_ORDER
p = P_CURVE


def om2(w):
    u, v = w
    return (v - u, -u)


def cube_root_unity(m):
    g = 2
    while pow(g, (m - 1) // 3, m) == 1:
        g += 1
    return pow(g, (m - 1) // 3, m)


def mi_bits(fs, ts, nf, nt):
    J = [[0] * nt for _ in range(nf)]
    for a, b in zip(fs, ts): J[a][b] += 1
    tot = len(fs)
    rs = [sum(r) for r in J]; cs = [sum(J[i][j] for i in range(nf)) for j in range(nt)]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
               for i in range(nf) for j in range(nt) if J[i][j] and rs[i] and cs[j])


def main():
    R1, R2 = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    R1, R2, DET, reduce_P, eis = make_lift(P_SECP, R1, R2)
    b1, b2 = cube_roots(P_SECP)
    beta = b1 if eis((b1 * 12345) % p) == reduce_P(*om2(eis(12345))) else b2
    R1t, R2t = tuple(R1), tuple(R2)

    def eps_of_x(x):
        U0 = eis(x); U1 = eis((beta * x) % p)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0): return 1        # 0-core -> 1
        if c == R1t or c == R2t: return 2
        if c == (-R1t[0], -R1t[1]) or c == (-R2t[0], -R2t[1]): return 0
        return 3

    lam = cube_root_unity(n)   # GLV scalar

    # sextic character tables mod n
    def chi_table(k):
        e = (n - 1) // k
        z = None
        for gg in range(2, 500):
            zz = pow(gg, e, n)
            if all(pow(zz, t, n) != 1 for t in range(1, k)) and pow(zz, k, n) == 1:
                z = zz; break
        return e, {pow(z, j, n): j for j in range(k)}
    e2, t2 = chi_table(2); e3, t3 = chi_table(3); e6, t6 = chi_table(6)

    def chi2(d): return t2[pow(d, e2, n)]
    def chi3(d): return t3[pow(d, e3, n)]
    def chi6(d): return t6[pow(d, e6, n)]

    labels = {
        "chi2(d)": (chi2, 2), "chi3(d)": (chi3, 3), "chi6(d)": (chi6, 6),
        "d%2": (lambda d: d % 2, 2), "d%3": (lambda d: d % 3, 3), "d%6": (lambda d: d % 6, 6),
    }

    # (1) GLV-invariance check: label(d) == label(lam*d)?
    print("(1) GLV-orbit invariance of each scalar label (rate label(d)==label(lam*d)):")
    rng = random.Random(3)
    chk = [rng.randrange(1, n) for _ in range(4000)]
    for name, (f, k) in labels.items():
        inv = sum(1 for d in chk if f(d) == f(lam * d % n)) / len(chk)
        print(f"    {name:9s}: invariant rate = {inv:.3f}  "
              f"({'ORBIT-INVARIANT -> candidate' if inv > 0.98 else 'orbit-varying -> washes out'})")

    # (2) sample eps(d) and labels; MI + scaling + control
    print("\n(2) eps(d) vs each label -- MI, scaling, shuffle control (secp, scalar_mul):")
    NMAX = 12000
    rng2 = random.Random(2024)
    E = []; L = {name: [] for name in labels}
    for _ in range(NMAX):
        d = rng2.randrange(1, n)
        pt = scalar_mul(d)
        if pt is None: continue
        E.append(eps_of_x(pt[0]))
        for name, (f, k) in labels.items():
            L[name].append(f(d))
    M = len(E)
    mc = Counter(E)
    print(f"    M={M}   eps marginal 0:{mc[0]/M:.3f} core:{mc[1]/M:.3f} +:{mc[2]/M:.3f} oth:{mc[3]/M:.3f}\n")
    for name, (f, k) in labels.items():
        tgt = L[name]
        rr = random.Random(hash(name) & 0xffff)
        zs = []
        for NN in [M // 3, 2 * M // 3, M]:
            obs = mi_bits(E[:NN], tgt[:NN], 4, k)
            nulls = [mi_bits(E[:NN], random.sample(tgt[:NN], NN), 4, k) for _ in range(120)]
            mu = sum(nulls) / len(nulls); sd = (sum((q - mu) ** 2 for q in nulls) / len(nulls)) ** 0.5
            zs.append((obs - mu) / sd if sd else 0.0)
        ct = tgt[:]; rr.shuffle(ct)
        cobs = mi_bits(E, ct, 4, k)
        cn = [mi_bits(E, random.sample(ct, M), 4, k) for _ in range(120)]
        cmu = sum(cn) / len(cn); csd = (sum((q - cmu) ** 2 for q in cn) / len(cn)) ** 0.5
        cz = (cobs - cmu) / csd if csd else 0.0
        print(f"    eps vs {name:9s}: z@M/3,2M/3,M = {zs[0]:+5.1f},{zs[1]:+5.1f},{zs[2]:+5.1f}"
              f"  control={cz:+4.1f}")
    print("\n  Predict (idea): chi2 invariant=candidate; chi3/chi6/d%3/d%6 orbit-varying")
    print("  ->wash out. All bounded by closure O(p^-1/2). A growing z + clean control on")
    print("  ANY (esp chi2) = eps predicts core/flap from d's multiplicative structure.")


if __name__ == "__main__":
    main()
