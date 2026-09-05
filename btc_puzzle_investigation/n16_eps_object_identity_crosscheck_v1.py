#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
n16_crosscheck_v1.py  —  the OWED N16 object-identity cross-check.

Question (CONFIRMED_core_gate_carry_epsilon_zero_v3, "owed"):
    is the proof script's  |u-v| <= 1/2  criterion the SAME object as the
    project's canonical  build.eps  (int1_frame_operator_v1.build_secp) ?

The two use different conventions (proof: omega + {pi, omega*pi} square domain;
build: omega^2 via om2 + Gauss-reduced basis, other cube root). This decides
whether CONFIRMED_v3's extension transfers to the rest of the project's eps work.

All signal-path arithmetic is exact integer. Float only for display.
"""
import random
from fractions import Fraction
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


# ---- canonical project object -------------------------------------------------
from int1_frame_operator_v1 import build_secp
from glv_fundamental_domain_law_v1 import P_SECP, AP_SECP, BP_SECP
EIS, EPS = build_secp()          # EPS = the canonical build.eps (0 core / 1,2 flap)

# ---- proof-script object (core_gate_carry_proof_v1), re-implemented verbatim --
p = 2**256 - 2**32 - 977
A_SP = 367917413016453100223835821029139468249
B_SP = 64502973549206556628585045361533709078
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

X135 = 0x145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16
X140 = 0x1f6a332d3c5c4f2de2378c012f429cd109ba07d69690c6c701b6bb87860d6640

def lift_uv(X):
    ku = (2 * X * (A_SP - B_SP) + p) // (2 * p)
    kv = (-2 * X * B_SP + p) // (2 * p)
    return X * (A_SP - B_SP) - ku * p, -X * B_SP - kv * p

def z_lift(X):
    u_num, v_num = lift_uv(X)
    ku = (X * (A_SP - B_SP) - u_num) // p
    kv = (-X * B_SP - v_num) // p
    return X - ku * A_SP + kv * B_SP, -ku * B_SP - kv * (A_SP - B_SP)

def omega_mul(z0, z1):
    return -z1, z0 - z1

def carry_c(X):
    z0, z1 = z_lift(X)
    w0, w1 = omega_mul(z0, z1)
    r0, r1 = z_lift(BETA * X % p)
    t0, t1 = w0 - r0, w1 - r1
    x_num = (A_SP - B_SP) * t0 + B_SP * t1
    y_num = -B_SP * t0 + A_SP * t1
    assert x_num % p == 0 and y_num % p == 0
    return x_num // p, y_num // p

def strip_pred(X):                       # proof's  |u-v| <= 1/2   (exact)
    u, v = lift_uv(X)
    return abs(u - v) <= p // 2

# ---- constants sanity ---------------------------------------------------------
print("=" * 84)
print(" N16 OBJECT-IDENTITY CROSS-CHECK:  |u-v|<=1/2  ==  build.eps ?")
print("=" * 84)
print(f"  proof A_SP == build AP_SECP : {A_SP == AP_SECP}")
print(f"  proof B_SP == build BP_SECP : {B_SP == BP_SECP}")
print(f"  proof p    == build P_SECP  : {p == P_SECP}")

# ---- the two real puzzle keys -------------------------------------------------
print("\n  real puzzle x-coords:")
for nm, X in [("#135", X135), ("#140", X140)]:
    e = EPS(X); s = strip_pred(X); c0 = (carry_c(X) == (0, 0))
    print(f"    {nm}: build.eps={e} (core={e==0}) | proof |u-v|<=1/2={s} | proof carry==0={c0} | "
          f"AGREE(eps0==strip)={ (e==0)==s }")

# ---- random battery -----------------------------------------------------------
M = 200_000
random.seed(20260818)
agree_strip = 0        # (build.eps==0) == (|u-v|<=1/2)
agree_carry = 0        # (build.eps==0) == (proof carry==0)
strip_eq_carry = 0     # (|u-v|<=1/2)  == (proof carry==0)   [internal proof T2]
n_eps0 = n_strip = n_pcarry0 = 0
mism_examples = []
for _ in range(M):
    X = random.randrange(1, p)
    e0 = (EPS(X) == 0)
    s = strip_pred(X)
    c0 = (carry_c(X) == (0, 0))
    n_eps0 += e0; n_strip += s; n_pcarry0 += c0
    agree_strip += (e0 == s)
    agree_carry += (e0 == c0)
    strip_eq_carry += (s == c0)
    if e0 != s and len(mism_examples) < 3:
        mism_examples.append((hex(X), EPS(X), s, c0))

print(f"\n  random battery  M = {M}  (exact integer comparisons)")
print(f"    core fractions: build.eps==0 {n_eps0/M:.6f} | proof |u-v|<=1/2 {n_strip/M:.6f} "
      f"| proof carry==0 {n_pcarry0/M:.6f}   (expect 0.75)")
print(f"    AGREE (build.eps==0) == (|u-v|<=1/2) : {agree_strip}/{M}   "
      f"[{'IDENTICAL' if agree_strip==M else 'MISMATCH'}]")
print(f"    AGREE (build.eps==0) == (proof carry==0): {agree_carry}/{M}   "
      f"[{'IDENTICAL' if agree_carry==M else 'MISMATCH'}]")
print(f"    AGREE (|u-v|<=1/2)  == (proof carry==0): {strip_eq_carry}/{M}   "
      f"[{'IDENTICAL' if strip_eq_carry==M else 'MISMATCH'}]  (proof-internal T2)")
if mism_examples:
    print("    first eps0!=strip mismatches (X, build.eps, strip, pcarry0):")
    for ex in mism_examples:
        print("      ", ex)
print("=" * 84)
