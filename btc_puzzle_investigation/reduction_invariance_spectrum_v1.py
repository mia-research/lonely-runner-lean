#!/usr/bin/env python3
"""
reduction_invariance_spectrum_v1.py — leak as REDUCTION, not revelation (user's reframe).

A computable readout F reduces the d-search USABLY only if its level sets {d:F(x_d)=v} are
cheaply ENUMERABLE = have coset/subgroup structure. Hard version: the invariance group
    Inv(F) = { k in (Z/nZ)^* : F(x_([kd]G)) = F(x_([d]G)) for ALL d }
(F invariant under scalar-mult by k => level sets are unions of <Inv(F)> orbits => factor
|Inv(F)| reduction). Known: mu_6 = <lambda,-1> from Aut(E). Anything LARGER = real reduction.

SOFT version (the "shadow of why D might be"): the near-invariance spectrum
    A_F(k) = (1/n) #{ d : F(x_[kd]) = F(x_d) }
k in mu_6 => A=1 (exact). Other k => chance (1/#values). An ANOMALOUS k with A >> chance =
d and kd PARTIALLY indistinguishable under F = a soft/statistical reduction = a shadow.

Trick: x_[kd] = xs[(k*d) mod n], so A_F(k) is pure index arithmetic on precomputed F-values
=> scan ALL k cheaply. Matched control: a RANDOM readout has no invariance beyond trivial.
Exact (sextant/eps/norm are exact integer lattice labels).
"""
import math
from fractions import Fraction as Fr
import numpy as np
from sympy import isprime
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import reduced_basis
from hybrid_char_sum_v1 import find_point, padd, mul, curve_points_order, legendre, tonelli


def prime_order_curve(lo, hi):
    for q in range(lo, hi):
        if isprime(q) and q % 3 == 1:
            m = q + 1
            for x in range(q):
                m += legendre((x**3 + 7) % q, q)
            if isprime(m):
                for x0 in range(1, q):
                    r = (x0**3 + 7) % q
                    if legendre(r, q) == 1:
                        return q, m, (x0, tonelli(r, q))
    return None


def orbit_xy(G, p, n):
    xs = [None] * n; ys = [None] * n; acc = None
    for d in range(1, n):
        acc = padd(acc, G, p); xs[d], ys[d] = acc
    return xs, ys


def main():
    p, n, G = prime_order_curve(500, 2000)
    print(f"y^2=x^3+7 / F_{p}, n={n} (prime).  LEAK = search-space REDUCTION.")
    xs, ys = orbit_xy(G, p, n)
    eis, eps = build(p)
    R1, R2 = reduced_basis(p); R1 = tuple(R1); R2 = tuple(R2); DET = R1[0]*R2[1]-R1[1]*R2[0]

    # GLV eigenvalue lambda (mult by lambda on scalar = beta on x)
    e = (p - 1) // 3; g = 2
    while pow(g, e, p) == 1: g += 1
    beta0 = pow(g, e, p); lam = None
    for bb in (beta0, beta0 * beta0 % p):
        for c in [c for c in range(2, n) if pow(c, 3, n) == 1]:
            if all(xs[(c * d) % n] == (bb * xs[d]) % p for d in range(1, 25)):
                lam = c; break
        if lam: break
    mu6 = sorted({1, n - 1, lam % n, (n - lam) % n, lam * lam % n, (n - lam * lam) % n})
    print(f"  GLV lambda={lam}; the KNOWN reduction group mu_6 = <lambda,-1> = {mu6}")

    # cheap readouts (functions of the point), precomputed over d
    def sextant(x):
        u, v = Fr(eis(x)[0]*R2[1]-eis(x)[1]*R2[0], DET), Fr(eis(x)[1]*R1[0]-eis(x)[0]*R1[1], DET)
        # 6 sectors by signs/order of (u,v,u+v) -- a mu_6 label
        return (u > 0, v > 0, (u + v) > 0)
    readouts = {}
    readouts["eps (3-val)"] = np.array([eps(xs[d]) if xs[d] is not None else 0 for d in range(n)])
    readouts["sextant (6-val)"] = np.array([hash(sextant(xs[d])) % 997 if xs[d] is not None else 0 for d in range(n)])
    readouts["norm-band(4)"] = np.array([(lambda u, v: int(4 * (u*u - u*v + v*v)))(*(Fr(eis(xs[d])[0]*R2[1]-eis(xs[d])[1]*R2[0], DET), Fr(eis(xs[d])[1]*R1[0]-eis(xs[d])[0]*R1[1], DET))) % 4 if xs[d] is not None else 0 for d in range(n)])
    readouts["y-parity(2)"] = np.array([ys[d] % 2 if ys[d] is not None else 0 for d in range(n)])
    rng = np.random.default_rng(0)
    readouts["[ctrl] random(6)"] = rng.integers(0, 6, size=n)

    ks = np.arange(1, n)
    idx = np.arange(n)
    rng2 = np.random.default_rng(7)
    print(f"\n  near-invariance A_F(k)=(1/n)#{{d:F(x_[kd])=F(x_d)}}. HARD: Inv(F). SOFT: max A off mu_6")
    print(f"  vs a DISTRIBUTION-MATCHED shuffle null (skew+extreme-value removed).")
    print(f"  {'readout':18} {'#vals':>5} {'|Inv|':>5} {'Inv=mu6 subgrp?':>15} "
          f"{'realMaxA':>9} {'shufMaxA(mean,p95)':>19} {'verdict':>10}")
    for name, F in readouts.items():
        F = np.asarray(F)[1:]                     # drop d=0
        m = n - 1
        nv = len(set(F.tolist()))
        def maxA_off(Fv):
            Fk = Fv[(np.outer(ks, np.arange(1, n)) % n) - 1]   # (n-1, n-1): F[k*d] for d=1..n-1
            A = (Fk == Fv[None, :]).mean(axis=1)
            inv = set((ks[A > 0.999]).tolist())
            offmask = np.array([k not in inv and k not in mu6 for k in ks])
            return (A[offmask].max() if offmask.any() else 0.0), inv
        realMax, inv = maxA_off(F)
        # shuffle null: permute F over d (kills k-structure, keeps value distribution)
        shuf = [maxA_off(rng2.permutation(F))[0] for _ in range(40)]
        sm, s95 = float(np.mean(shuf)), float(np.quantile(shuf, 0.95))
        issub = inv <= set(mu6)
        verdict = "SHADOW?" if realMax > s95 + 0.02 else "no shadow"
        print(f"  {name:18} {nv:>5} {len(inv):>5} {str(issub):>15} "
              f"{realMax:>9.4f} {sm:>8.4f},{s95:>8.4f}  {verdict:>10}")
    print(f"\n  READ: Inv(F) subset of mu_6 for ALL geometric readouts => the ONLY HARD (usable,")
    print(f"  enumerable) reduction is the known automorphism factor |Aut|<=6. realMaxA <= shuffle")
    print(f"  null => NO soft/partial shadow (d,kd not partially indistinguishable beyond mu_6).")
    print(f"  realMaxA >> shuffle-p95 at some off-mu6 k WOULD be a genuine sub-automorphism reduction.")


if __name__ == "__main__":
    main()
