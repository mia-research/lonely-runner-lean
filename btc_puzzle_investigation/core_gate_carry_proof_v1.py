#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
core_gate_carry_proof_v1.py
===========================
End-to-end numerical verification of the EXACT coordinate-side carry picture
for the Eisenstein lift on secp256k1.

Objects (all public, all functions of x alone):
  z(X)   = lift of X in the square fundamental domain D of the lattice (pi),
           in b-coordinates (u, v) in [-1/2, 1/2]^2, basis {pi, omega*pi}.
  s(X)   = u^2 - u v + v^2 = N(z(X))/p            (the "core gate" statistic)
  c(X)   = (omega*z(X) - z(beta*X)) / pi in Z[omega]   (the "carry"; eps=0
           in the external documents means c = (0,0))

Claims verified (each is proved in NOTE_core_gate_exact_carry_region_v1.md):
  T1  s < 3/16  ==>  c = (0,0)                        [gate sufficiency]
  T2  c = (0,0)  <=>  (u,v) in the hexagon H = D ∩ {|u-v| <= 1/2}
  T3  Pr[c = 0] = area(H) = 3/4                       [exact, not measured]
  T4  {s < 3/16} = inscribed ellipse of H (tangent to all 6 sides);
      3/16 is sharp (carry region starts exactly at s = 3/16, at (1/4,-1/4))
  T5  c = (0,0)  ==>  s <= 1/4                         [necessary side]
  T6  direct computation on the real puzzle x-coordinates: c = (0,0)

Pure stdlib. Deterministic (seeded).
"""
import random
from fractions import Fraction

random.seed(20260816)

p = 2**256 - 2**32 - 977
A_SP = 367917413016453100223835821029139468249
B_SP = 64502973549206556628585045361533709078
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee  # omega mod pi

X135 = 0x145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16
X140 = 0x1f6a332d3c5c4f2de2378c012f429cd109ba07d69690c6c701b6bb87860d6640


def lift_uv(X):
    """(u_num, v_num) with u = u_num/p, v = v_num/p the b-coords of the lift."""
    ku = (2 * X * (A_SP - B_SP) + p) // (2 * p)
    kv = (-2 * X * B_SP + p) // (2 * p)
    return X * (A_SP - B_SP) - ku * p, -X * B_SP - kv * p


def z_lift(X):
    u_num, v_num = lift_uv(X)
    ku = (X * (A_SP - B_SP) - u_num) // p
    kv = (-X * B_SP - v_num) // p
    z0 = X - ku * A_SP + kv * B_SP
    z1 = -ku * B_SP - kv * (A_SP - B_SP)
    assert (z0 + z1 * BETA - X) % p == 0
    return z0, z1


def s_num(X):
    """exact s * p^2."""
    u, v = lift_uv(X)
    return u * u - u * v + v * v


def omega_mul(z0, z1):
    return -z1, z0 - z1


def carry_c(X):
    """c = (omega*z(X) - z(beta X)) / pi  in Z[omega]; returns (x, y) coeffs."""
    z0, z1 = z_lift(X)
    w0, w1 = omega_mul(z0, z1)
    r0, r1 = z_lift(BETA * X % p)
    t0, t1 = w0 - r0, w1 - r1
    x_num = (A_SP - B_SP) * t0 + B_SP * t1
    y_num = -B_SP * t0 + A_SP * t1
    assert x_num % p == 0 and y_num % p == 0, "pi-divisibility failed"
    return x_num // p, y_num // p


print("=" * 84)
print(" EXACT COORDINATE-SIDE CARRY: THEOREM VERIFICATION (secp256k1)")
print("=" * 84)

# T6 first: the real puzzles, by DIRECT computation (no gate needed)
for name, X in [("x135", X135), ("x140", X140)]:
    c = carry_c(X)
    s = Fraction(s_num(X), p * p)
    print(f"  {name}: s = {float(s):.12f}   carry c = {c}   eps=0 by DIRECT computation: {c == (0, 0)}")

M = 200000
gate_viol = 0            # T1 violations
strip_mismatch = 0       # T2 mismatches
n_c0 = 0
min_s_nonzero = None     # sharpness of 3/16 (min s*p^2 among c != 0)
max_s_zero = 0           # T5 (max s*p^2 among c == 0)
for _ in range(M):
    X = random.randrange(1, p)
    sn = s_num(X)
    c = carry_c(X)
    in_strip = abs((lift_uv(X)[0] - lift_uv(X)[1])) <= p // 2
    if sn * 16 < 3 * p * p and c != (0, 0):
        gate_viol += 1
    if (c == (0, 0)) != in_strip:
        strip_mismatch += 1
    if c == (0, 0):
        n_c0 += 1
        max_s_zero = max(max_s_zero, sn)
    else:
        if min_s_nonzero is None or sn < min_s_nonzero:
            min_s_nonzero = sn

print(f"\n  T1  gate sufficiency s<3/16 ==> c=0 : violations {gate_viol}/{M}")
print(f"  T2  c=0 <=> hexagon strip |u-v|<=1/2: mismatches {strip_mismatch}/{M}")
print(f"  T3  Pr[c=0] empirical = {n_c0 / M:.6f}   exact = 3/4 = 0.750000")
print(f"  T4  sharpness: min s among c!=0 = {min_s_nonzero / (p * p):.9f}  (threshold 3/16 = 0.1875)")
print(f"  T5  max s among c=0  = {max_s_zero / (p * p):.9f}  (bound 1/4 = 0.25)")

# T4 geometry: tangency points (exact rationals)
for (uu, vv), side in [((Fraction(1, 2), Fraction(1, 4)), "u=1/2"),
                       ((Fraction(1, 4), Fraction(-1, 4)), "u-v=1/2"),
                       ((Fraction(1, 2), Fraction(0)), "hexagon vertex")]:
    q = uu * uu - uu * vv + vv * vv
    print(f"  q({uu},{vv}) [on {side}] = {q}  (= {float(q)})")
print("=" * 84)
