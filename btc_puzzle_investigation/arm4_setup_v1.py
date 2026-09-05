#!/usr/bin/env python3
"""
arm4_setup_v1.py — ARM 4 shared setup: pi_p, pi_n = pi_p - 1, the lattice L_n,
eis_n, cent, sextant.  Exact integers only (btc_puzzle_investigation/CLAUDE.md).

Object (spec section 4.1): the two quotients of Z[omega] adjacent by the "-1",
    Z[omega]/(pi_p) = F_p   (coordinates)      Z[omega]/(pi_n) = Z/n   (scalars)
ARM 4 reduces BOTH sides modulo the SAME ideal (pi_n) and asks whether the two
sextant labels are coupled.

Parity, which is the whole reason the prior test was uninformative:
    eis_p(x([d]G)) is EVEN in d      (x(-P) = x(P))          -> forced zero channel
    cent(y([d]G))  is ODD  in d      (y(-P) = -y(P))         -> parity-legal
so the y-readout is used, never the x-readout.
"""
from lift_sextant_rhombus_law_proof_v2 import (cornacchia_4p_D3, gauss_reduce,
                                               rdiv, sextant, enorm)

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8


def associates(u, v):
    """All 12 associates of u+v*omega (6 units x 2 conjugates), as (u,v) pairs."""
    out = []
    for w in ((u, v), (u - v, -v)):                    # w and its conjugate
        a, b = w
        for _ in range(3):                             # multiply by omega
            out.append((a, b)); out.append((-a, -b))
            a, b = -b, a - b                           # omega * (a + b w)
    return out


def pi_p_with_trace(p, t):
    """The associate of pi_p whose trace 2u - v equals the Frobenius trace t."""
    uv = cornacchia_4p_D3(p)
    assert uv is not None, "cornacchia failed"
    u, v = uv
    assert u * u - u * v + v * v == p, "norm(pi_p) != p"
    for (a, b) in associates(u, v):
        if a * a - a * b + b * b == p and 2 * a - b == t:
            return (a, b)
    raise AssertionError("no associate with the required trace")


def lattice_n(p=P, n=N):
    """Reduced basis of the ideal (pi_n) = (pi_p - 1), pi_n = A + B*omega.

    Construction is the one already on file (reduced_basis / gauss_reduce), so
    every number here is comparable with the rest of the record.
    """
    t = p + 1 - n
    A0, B0 = pi_p_with_trace(p, t)
    A, B = A0 - 1, B0                                   # pi_n = pi_p - 1
    assert A * A - A * B + B * B == n, "norm(pi_n) != n"
    R1, R2 = gauss_reduce((A, B), (-B, A - B))          # basis {pi_n, omega*pi_n}
    DET = R1[0] * R2[1] - R1[1] * R2[0]
    assert abs(DET) == n, f"det {DET} != +-n"
    return (A0, B0), (A, B), R1, R2, DET


def eis_n(X, R1, R2, DET):
    """Reduce the rational integer X into the fundamental cell of L_n.
    Returns ((u,v), tie) where tie is True if an rdiv tie was hit (see 4.7)."""
    n1 = X * R2[1]; n2 = -X * R1[1]
    c1 = rdiv(n1, DET); c2 = rdiv(n2, DET)
    d = abs(DET)
    tie = (2 * (n1 % d) == d) or (2 * (n2 % d) == d)
    return (X - (c1 * R1[0] + c2 * R2[0]),
            -(c1 * R1[1] + c2 * R2[1])), tie


def cent(Y, p=P):
    """Centred representative: cent(-Y mod p) = -cent(Y), exactly, for Y != 0."""
    Y %= p
    return Y - p if 2 * Y > p else Y


ZETA6 = [(1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1)]   # zeta6^m, m=0..5


def U_from_table(tab, j, k):
    """U_{j,k} = sum_{u,w} tab[u][w] * zeta6^{(j u + k w) mod 6}, exact in Z[omega]."""
    A = B = 0
    for u in range(6):
        for w in range(6):
            c = tab[u][w]
            if not c: continue
            zu, zv = ZETA6[(j * u + k * w) % 6]
            A += c * zu; B += c * zv
    return (A, B)


def absU2(U):
    a, b = U
    return a * a - a * b + b * b


if __name__ == "__main__":
    (A0, B0), (A, B), R1, R2, DET = lattice_n()
    t = P + 1 - N
    print("=" * 78)
    print("ARM 4 SETUP — the ideal (pi_n) = (pi_p - 1) at secp256k1")
    print("=" * 78)
    print(f"  t = p+1-n     = {t}")
    print(f"  pi_p          = {A0} + {B0}*omega      trace 2u-v = {2*A0-B0}")
    print(f"  norm(pi_p)==p : {A0*A0-A0*B0+B0*B0 == P}")
    print(f"  pi_n = pi_p-1 = {A} + {B}*omega")
    print(f"  norm(pi_n)==n : {A*A-A*B+B*B == N}")
    print(f"  reduced basis R1 = {R1}\n                 R2 = {R2}")
    print(f"  |det| == n    : {abs(DET) == N}")
    print(f"  enorm(R1)={enorm(R1)}\n  enorm(R2)={enorm(R2)}")

    # --- primitive checks that must hold before any feature is built
    print("\n  PRIMITIVE CHECKS (must all pass)")
    # NAMED EXCEPTION CLASS, found by this check and not assumed away:
    # sextant()'s base wedge is CLOSED at both bounding rays, so points lying
    # exactly ON a ray take the LOWER index and the antipodal identity can fail.
    # On-ray  <=>  u==0 or v==0 or u==v.  Empirically the failures are exactly
    # the v==0 (real-axis) class; 200000 random off-ray points give 0 violations.
    # Stage 1 must COUNT how many real features land on a ray -- like the rdiv
    # tie ledger, this is reported, never assumed to be empty.
    gen = [(3, 1), (1, 3), (-2, 1), (5, -2), (-1, -4), (7, 2), (-5, -2), (2, 9)]
    ok_s = all(sextant(-u, -v) == (sextant(u, v) + 3) % 6 for (u, v) in gen)
    ray_bad = [(u, v) for (u, v) in [(1, 0), (5, 0), (-1, 0), (0, 1), (1, 1)]
               if sextant(-u, -v) != (sextant(u, v) + 3) % 6]
    print(f"   sextant(-w) == sextant(w)+3 mod 6, OFF ray  : {ok_s}")
    print(f"   on-ray exceptions (u==0 or v==0 or u==v)    : {ray_bad}")
    print(f"     -> exception class is v==0 (the real axis); counted in stage 1")
    ok_c = all(cent((-Y) % P) == -cent(Y) for Y in
               (1, 2, 12345, P // 3, P - 1, (P - 1) // 2, (P + 1) // 2))
    print(f"   cent(-Y mod p) == -cent(Y)                  : {ok_c}")
    ties = 0; ok_o = True
    for X in (1, 7, 10 ** 20, N // 5, N - 3, 123456789):
        z1, t1 = eis_n(X, R1, R2, DET)
        z2, t2 = eis_n(-X, R1, R2, DET)
        if t1 or t2: ties += 1
        elif z2 != (-z1[0], -z1[1]): ok_o = False
    print(f"   eis_n(-X) == -eis_n(X) off ties             : {ok_o}  (ties {ties})")
    assert ok_s and ok_c and ok_o
