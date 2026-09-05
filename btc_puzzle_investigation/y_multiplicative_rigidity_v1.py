#!/usr/bin/env python3
"""
y_multiplicative_rigidity_v1.py

Closes the basis gap flagged in the RH-framework review: my earlier chi2(y) null was
measured in the ADDITIVE basis (Fourier over d->d+k). This tests the MULTIPLICATIVE
basis and a residue-dictionary GRAM/RIGIDITY operator (the 'backdoor' instrument from
the phi(n)-residue rigidity preprint).

  Part 1 (multiplicative harmonic): correlate f(d)=chi2(y([d]G)) with low-order
    multiplicative characters psi_m of (Z/n)*, m | (n-1). Symmetry-aware: f is odd
    under -1 and invariant under lambda, so psi_m can correlate ONLY if psi_m(-1)=-1
    and psi_m(lambda)=1; others are forced to 0.
  Part 2 (rigidity Gram): regress f on the residue dictionary {one-hot(d mod q):
    q in Q0={3,5,7,11,13}} jointly. R^2 = coherent fraction. Compare to permutation
    null and power-scale. Coherent mode surviving => structure; rigid (R^2~null) => DLP.

Expected: flat/rigid (the forced symmetries + DLP argue for it) -- but this is the
untested basis, stated up front, measured not asserted.
"""
import numpy as np, random, math
from ecc_secp256k1 import P as p, N_ORDER as n, scalar_mul

fac_n1 = [2, 3, 149, 631, 107361793816595537, 174723607534414371449,
          341948486974166000522343609283189]

def primitive_root(n, factors):
    for g in range(2, 200):
        if all(pow(g, (n - 1) // q, n) != 1 for q in factors):
            return g
    raise RuntimeError

def chi2(v): return 1.0 if pow(int(v), (p - 1) // 2, p) == 1 else -1.0

def main():
    g = primitive_root(n, fac_n1)
    # lambda = order-3 element
    lam = pow(g, (n - 1) // 3, n)
    print(f"primitive root g={g};  lambda (order 3) fixed.")

    M = 30000
    rng = random.Random(7)
    D = [rng.randrange(1, n) for _ in range(M)]
    F = np.array([chi2(scalar_mul(d)[1]) for d in D])
    Dobj = np.array(D, dtype=object)
    floor = 1 / math.sqrt(M)
    print(f"M={M}  mean f={F.mean():+.4f}  floor 1/sqrt(M)={floor:.4f}\n")

    # ---- Part 1: multiplicative characters psi_m ----
    print("Part 1  MULTIPLICATIVE characters  c_m = |E[f(d) psi_m(d)]|:")
    for m in (2, 3, 6, 149, 631):
        e = (n - 1) // m
        zeta = pow(g, e, n)
        table = {pow(zeta, j, n): j for j in range(m)}
        # symmetry: allowed iff psi_m(-1)=-1 and psi_m(lambda)=1
        j_m1 = table[pow(n - 1, e, n)]; j_lam = table[pow(lam, e, n)]
        odd = (2 * j_m1) % m == m % 2 * 0 + (m // 2) * 2 % m and j_m1 == (m // 2 if m % 2 == 0 else -1)
        allowed = (j_m1 == (m // 2) if m % 2 == 0 else False) and (j_lam == 0)
        j = np.array([table[pow(int(d), e, n)] for d in Dobj])
        psi = np.exp(2j * math.pi * j / m)
        c = abs(np.mean(F * psi))
        note = "ALLOWED (odd & lambda-inv)" if allowed else "forced~0 by symmetry"
        print(f"  order {m:>3}: |c_m|={c:.4f}  (floor {floor:.4f})  psi(-1)=zeta^{j_m1}, psi(lam)=zeta^{j_lam}  [{note}]")

    # ---- Part 2: rigidity Gram -- regress f on residue dictionary {d mod q} ----
    print("\nPart 2  RIGIDITY GRAM  (regress f on residue dictionary {d mod q}, q in Q0):")
    Q0 = [3, 5, 7, 11, 13]
    def design(Dsub):
        cols = []
        for q in Q0:
            r = np.array([int(d) % q for d in Dsub])
            for a in range(q - 1):                     # q-1 one-hot cols (drop last, centered)
                cols.append((r == a).astype(float))
        Xd = np.array(cols).T
        return Xd - Xd.mean(0)
    def r2(Xd, y):
        y = y - y.mean()
        beta, *_ = np.linalg.lstsq(Xd, y, rcond=None)
        yhat = Xd @ beta
        return float((yhat @ yhat) / (y @ y))
    Ms = [7500, 15000, 30000]
    rr = np.random.default_rng(3)
    print("  R^2 of f on the joint residue dictionary, vs permutation null, growing M:")
    for M2 in Ms:
        Xd = design(Dobj[:M2]); y = F[:M2]
        obs = r2(Xd, y)
        null = np.array([r2(Xd, y[rr.permutation(M2)]) for _ in range(60)])
        z = (obs - null.mean()) / (null.std() + 1e-12)
        print(f"    M={M2:6d}: R^2={obs:.5f}  null_mean={null.mean():.5f}  z={z:+.1f}  "
              f"(dof={Xd.shape[1]}; coherent if R^2>>null AND grows)")
    print("  => R^2 tracking null with no growth = RIGID (residue dictionary carries no")
    print("     coherent mode predicting chi2(y)); a surviving low-complexity mode would be a signal.")

    # ---- Part 2b: MULTIPLICATIVE residue dictionary (Legendre/cubic of d mod q) ----
    print("\nPart 2b  multiplicative residue features (Legendre & cubic symbols of d mod q):")
    def mult_design(Dsub):
        cols = []
        for q in [5, 7, 11, 13, 149, 631]:
            leg = np.array([pow(int(d) % q, (q - 1) // 2, q) if int(d) % q else 0 for d in Dsub], float)
            cols.append(leg - leg.mean())
            if (q - 1) % 3 == 0:
                cub = np.array([1.0 if (int(d) % q) and pow(int(d) % q, (q - 1) // 3, q) == 1 else 0.0 for d in Dsub])
                cols.append(cub - cub.mean())
        return np.array(cols).T
    Xm = mult_design(Dobj); obs = r2(Xm, F)
    null = np.array([r2(Xm, F[rr.permutation(M)]) for _ in range(60)])
    z = (obs - null.mean()) / (null.std() + 1e-12)
    print(f"  R^2={obs:.5f}  null_mean={null.mean():.5f}  z={z:+.1f}  (dof={Xm.shape[1]})")

if __name__ == "__main__":
    main()
