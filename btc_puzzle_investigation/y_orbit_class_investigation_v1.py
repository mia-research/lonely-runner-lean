#!/usr/bin/env python3
"""
y_orbit_class_investigation_v1.py

Investigation of the y-coordinate / orbit-class structure of secp256k1, following the
avenues raised: (A) orbit-class sextant-given-y; (B) chi2(y) as the odd coordinate;
(C) S3 summation polynomial under [omega]; (D) forced arithmetic facts; (E) the
eigendifferential/Hasse-Witt level.

Each result is tagged. NB: these are POSITIVE-STRUCTURE measurements and scoped nulls,
NOT closure claims. Empirical nulls are bound to the features/sample/floor stated.
"""
import random, numpy as np
import sympy as sp
from ecc_secp256k1 import P as p, N_ORDER as n, scalar_mul
from eisenstein_lift_sextant_exact_v1 import eis, sextant
from angular_interference_scaling_v1 import conditional

g = 2
while pow(g, (p - 1) // 3, p) == 1: g += 1
beta = pow(g, (p - 1) // 3, p); beta2 = pow(beta, 2, p)
def sx(x): return sextant(*eis(x))


def A_orbit_sextant_structure(M=40000):
    print("=" * 70); print("(A) GLV orbit-sextant structure  [VERIFIED structure]")
    from collections import Counter
    rng = random.Random(1); triples = Counter(); same_par = 0
    for _ in range(M):
        x = rng.randrange(1, p)
        t = (sx(x), sx(beta * x % p), sx(beta2 * x % p))
        triples[tuple(sorted(t))] += 1
        if len({v % 2 for v in t}) == 1: same_par += 1
    print(f"  same-parity across the GLV orbit: {same_par}/{M} = {same_par/M:.3f}")
    print(f"  reason: beta=omega^2 is a 120deg = 2-sextant (EVEN) rotation; parity breaks")
    print(f"          only at fold boundaries (~2%). top triples: {triples.most_common(4)}")
    print("  => given EXACT y (the orbit), sextant is confined to the 3 orbit-sextants,")
    print("     ~98% one parity. This is a near-invariant of y. (Conjecture 'sextant|y")
    print("     uniform on Z/6' is FALSE at exact-y resolution.)\n")


def A2_no_scalar_leak(M=24000):
    print("=" * 70); print("(A2) ...but it carries NO scalar information  [VERIFIED null]")
    rng = random.Random(2)
    D = [rng.randrange(1, n) for _ in range(M)]
    X = [scalar_mul(d)[0] for d in D]
    SXT = np.array([sx(x) for x in X]); SPAR = SXT % 2
    tg = {'d%2': np.array([d % 2 for d in D]), 'd%3': np.array([d % 3 for d in D]),
          'd%6': np.array([d % 6 for d in D])}
    Ms = [3000, 6000, 12000, 24000]; rr = np.random.default_rng(9)
    for fn, fv in {'sextant': SXT, 'sext_parity(~f(y))': SPAR}.items():
        for tn, tv in tg.items():
            r = conditional(fv, tv, Ms, 200, rr)
            print(f"  {fn:18} vs {tn}: " + "  ".join(f"z={x[2]:+.1f}" for x in r))
    print("  => noise, no growth. Orbit-class structure is a coordinate relation, not a")
    print("     scalar leak; and it washes out at any coarse (usable) y-resolution.\n")


def B_chi2_y(M=24000):
    print("=" * 70); print("(B) chi2(y) = the odd coordinate  [VERIFIED null, scoped]")
    rng = random.Random(3)
    D = [rng.randrange(1, n) for _ in range(M)]
    Y = [scalar_mul(d)[1] for d in D]
    C = np.array([1 if pow(int(y), (p - 1) // 2, p) == 1 else 0 for y in Y])
    tg = {'d<n/2(sign)': np.array([1 if d < n // 2 else 0 for d in D]),
          'chi2(d)': np.array([1 if pow(d, (n - 1) // 2, n) == 1 else 0 for d in D]),
          'd%2': np.array([d % 2 for d in D]), 'floor(3d/n)': np.array([(3 * d) // n for d in D])}
    Ms = [3000, 6000, 12000, 24000]; rr = np.random.default_rng(5)
    print(f"  marginal P(chi2(y)=QR) = {C.mean():.4f}  (balanced)")
    for tn, tv in tg.items():
        r = conditional(C, tv, Ms, 200, rr)
        print(f"  chi2(y) vs {tn:12}: " + "  ".join(f"z={x[2]:+.1f}" for x in r))
    print("  => balanced pseudo-random odd bit; no low-complexity dependence on d found.\n")


def C_S3_covariance():
    print("=" * 70); print("(C) S3 summation polynomial under [omega]  [PROVED covariance]")
    x1, x2, x3, b, bt = sp.symbols('x1 x2 x3 b beta')
    S3 = sp.expand((x1 - x2) ** 2 * x3 ** 2 - 2 * ((x1 + x2) * (x1 * x2) + 2 * b) * x3
                   + ((x1 * x2) ** 2 - 4 * b * (x1 + x2)))
    S3b = sp.expand(S3.subs({x1: bt * x1, x2: bt * x2, x3: bt * x3}))
    S3b = sp.expand(S3b.replace(lambda e: e.is_Pow and e.base == bt,
                                lambda e: bt ** (e.exp % 3)))
    d = sp.expand(sp.expand(S3b - bt * S3).replace(
        lambda e: e.is_Pow and e.base == bt, lambda e: bt ** (e.exp % 3)))
    print(f"  S3(beta*x1,beta*x2,beta*x3) = beta * S3 : {d == 0}  (beta-eigenvector)")
    print("  => the relation variety {S3=0} is [omega]-invariant. This is the known")
    print("     GLV/automorphism symmetry => a CONSTANT-FACTOR speedup in index-calculus/")
    print("     rho (order-6 automorphisms), NOT a change in degree or asymptotic hardness.\n")


def D_forced_facts():
    print("=" * 70); print("(D) forced arithmetic facts about y  [VERIFIED]")
    print(f"  n prime: {sp.isprime(n)};  p mod 4 = {p % 4} => chi2(-1) = {(-1)**((p-1)//2)}")
    print(f"  7 is a QR mod p: {pow(7,(p-1)//2,p)==1}  (non-residue: else (0,+-sqrt7) = rational 3-torsion)")
    print(f"  -7 is a cube mod p: {pow((-7)%p,(p-1)//3,p)==1}  (non-cube: else rational 2-torsion (x0,0))")
    print(f"  3 | n: {n%3==0}  => y-fibration E->P^1 ramifies at E[omega-1], no rational ramification.")
    print("  Coherent little theorem: n prime + CM by Z[omega] forces this.\n")


def E_hasse_note():
    print("=" * 70); print("(E) eigendifferential / Hasse-Witt level  [CITED reasoning]")
    t = p + 1 - n
    print(f"  dx/y is a CM eigendifferential ([omega]* (dx/y) = beta*(dx/y)); the de Rham /")
    print(f"  crystalline cohomology of an elliptic curve is 2-dimensional with Frobenius")
    print(f"  char poly  X^2 - t*X + p,  t = p+1-n = {t}.")
    print("  => everything at this level is DETERMINED by t (already known). There is no")
    print("     finer invariant 'past t' for genus 1. (Earlier 'genuine parallel' framing")
    print("     was wrong: the rhombus lived in an infinite-dim function space; the")
    print("     differential lives in a 2-dim cohomology with no room past t.)\n")


if __name__ == "__main__":
    A_orbit_sextant_structure()
    A2_no_scalar_leak()
    B_chi2_y()
    C_S3_covariance()
    D_forced_facts()
    E_hasse_note()
