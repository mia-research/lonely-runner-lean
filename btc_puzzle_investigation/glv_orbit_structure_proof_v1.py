#!/usr/bin/env python3
"""
glv_orbit_structure_proof_v1.py

Closed-form action of the secp256k1 GLV endomorphism on the single-x shadows,
completing the "single-x structure" map (rhombus law + chi6 uniform law).

GLV endomorphism:  phi(x,y) = (beta*x, y),  beta^3 = 1, beta != 1  (a nontrivial
cube root of unity mod p);  on scalars  [lambda]P = phi(P),  lambda^2+lambda+1 = 0
mod N_ORDER.  The GLV triple of a key d is { [d]G, [lambda d]G, [lambda^2 d]G },
whose x-coordinates are { x, beta*x, beta^2*x }.

PROVEN / VERIFIED here (exact arithmetic):

  (A) beta == omega^2 (mod pi_p).  Since F_p ~ Z[omega]/(pi_p) sends omega -> a
      root of X^2+X+1, and beta is exactly such a root, the GLV endomorphism IS
      "multiply the lift by a primitive cube root of unity" -- the CM-by-Z[omega]
      origin of secp's GLV.

  (B) MULTIPLICATIVE shadow transforms by a CONSTANT SHIFT (exact, all x):
        chi6(beta x) = chi6(x) + 4  (mod 6)
        chi3(beta x) = chi3(x) + 1  (mod 3)
        chi2(beta x) = chi2(x)          (beta is a QR)
      => on a GLV triple {x,beta x,beta^2 x}:  chi3 realizes ALL THREE classes
      {0,1,2} exactly once; chi6 realizes the three residues of FIXED PARITY
      {c, c+2, c+4}; chi2 is constant.  (chi6 = (chi2,chi3) by CRT on Z/6.)

  (C) GEOMETRIC shadow (lift sextant) does NOT transform cleanly: multiplication
      by omega^2 rotates the lattice 120deg = +4 sextants, but P is a RHOMBUS
      (180deg-symmetric, not 120deg), so the reduction back into P folds. Measured:
      sextant shift is +4 ~75% / +0 ~23% / boundary ~2%. No clean law.

  (D) y is FIXED by GLV (phi preserves y; x^3+7 is GLV-invariant since beta^3=1).
      => GLV gives ZERO leverage on any y-coordinate / group-law functional.

Consequence: the single-x space is charted. Multiplicative readouts are governed by
character theory (uniform marginals, clean GLV shifts); the one non-uniform readout
(sextant) is the rhombus area law and is GLV-tangled; y is GLV-invariant. The
remaining structure lives OFF the single-x axis: joint/multi-point across INDEPENDENT
keys (GLV only gives the degenerate deterministic triple), and y / group-law.
"""
import random
from ecc_secp256k1 import P as p, scalar_mul, N_ORDER
from angular_interference_scaling_v1 import chi6, chi3
from eisenstein_lift_sextant_exact_v1 import eis, sextant

aP = 367917413016453100223835821029139468249
bP = 303414439467246543595250775667605759171
assert aP * aP - aP * bP + bP * bP == p


def cube_root_unity_mod(m):
    g = 2
    while pow(g, (m - 1) // 3, m) == 1:
        g += 1
    return pow(g, (m - 1) // 3, m)


def main():
    beta = cube_root_unity_mod(p)
    print("GLV constant beta:")
    print(f"  beta^3==1, beta!=1: {pow(beta, 3, p) == 1 and beta != 1}"
          f"   beta^2+beta+1==0: {(beta * beta + beta + 1) % p == 0}")

    # (A) beta == omega^2 mod pi_p   (omega ≡ -aP/bP from aP + bP*omega ≡ 0)
    omega = (-aP * pow(bP, -1, p)) % p
    branch = "omega" if beta == omega else ("omega^2" if beta == omega * omega % p else "??")
    print(f"\n(A) beta == {branch} (mod pi_p)  => GLV = multiply lift by a primitive "
          f"cube root of unity (CM by Z[omega]).")

    # phi(x,y)=(beta x, y) and x^3+7 GLV-invariant, on a real curve point
    x1, y1 = scalar_mul(12345)
    lam = cube_root_unity_mod(N_ORDER)
    xr, yr = scalar_mul(12345 * lam % N_ORDER)
    print(f"    phi check: x([lam]P) in {{beta*x, beta^2*x}}: "
          f"{xr in (beta * x1 % p, pow(beta, 2, p) * x1 % p)}   y preserved: "
          f"{yr in (y1, (p - y1) % p)}")
    print(f"(D) x^3+7 GLV-invariant (beta^3=1): "
          f"{(pow(beta * x1 % p, 3, p) + 7) % p == (pow(x1, 3, p) + 7) % p}  "
          f"=> y fixed by GLV; no leverage on y/group-law.")

    # (B) exact constant shifts of the multiplicative characters
    c6, c3 = chi6(beta), chi3(beta)
    rng = random.Random(3)
    ok6 = ok3 = ok2 = True
    N = 40000
    for _ in range(N):
        x = rng.randrange(1, p)
        if (chi6(beta * x % p) - chi6(x)) % 6 != c6: ok6 = False
        if (chi3(beta * x % p) - chi3(x)) % 3 != c3: ok3 = False
        if pow(beta * x % p, (p - 1) // 2, p) != pow(x, (p - 1) // 2, p): ok2 = False
    print(f"\n(B) multiplicative shadow, EXACT over {N} x:")
    print(f"    chi6(beta x) = chi6(x) + {c6} (mod 6): {ok6}")
    print(f"    chi3(beta x) = chi3(x) + {c3} (mod 3): {ok3}  => GLV triple hits all 3 cubic classes")
    print(f"    chi2 invariant: {ok2}  => chi6 triple = {{c, c+2, c+4}} (fixed parity)")

    # (C) geometric shadow: no clean shift (rhombus 180deg-only symmetry)
    from collections import Counter
    d = Counter()
    for _ in range(40000):
        x = rng.randrange(1, p)
        u, v = eis(x); u2, v2 = eis(beta * x % p)
        d[(sextant(u2, v2) - sextant(u, v)) % 6] += 1
    tot = sum(d.values())
    dist = {k: round(v / tot, 3) for k, v in sorted(d.items())}
    print(f"\n(C) geometric shadow (sextant) shift under GLV: {dist}")
    print(f"    max mass {max(d.values()) / tot:.2f} < 1 => FOLD-TANGLED: multiplication by "
          f"omega^2 is 120deg rotation but P is a 180deg-symmetric rhombus, so the")
    print(f"    reduction into P folds. The geometric shadow does NOT respect GLV.")


if __name__ == "__main__":
    main()
