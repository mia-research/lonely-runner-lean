#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
glv_orbit_carry_conservation_v1.py
==================================
Three new public-side theorems that follow from the exact carry machinery
(NOTE_core_gate_exact_carry_region_v1.md), all verified exactly here:

T1  CLOSED FORM + EXACT LAW of the carry: in b-coordinates,
      c(X) = (0, floor(u - v + 1/2))      -- the carry is the integer overflow
                                           of the single linear form u - v;
    hence c takes exactly three values 0, +omega, -omega with probabilities
      Pr[c=0] = 3/4,  Pr[c=+omega] = Pr[c=-omega] = 1/8   (exact).

T2  ORBIT CONSERVATION LAW:
      omega^2 c(X) + omega c(beta X) + c(beta^2 X) = 0   in Z[omega],
    which, with the 3-value law, forces the TRICHOTOMY
      (c(X), c(beta X), c(beta^2 X)) in {(0,0,0), (w,w,w), (-w,-w,-w)}.
    The carry is a GLV-orbit INVARIANT; the two corner triangles are
    orbit-invariant sets.

T3  NORM ORBIT-INVARIANCE: c = 0  ==>  s(beta X) = s(beta^2 X) = s(X) exactly.
    For c = eps*omega (eps = +-1): z(beta X) = omega*(z - eps*pi), so
      N(z(beta X)) = N(z - eps*pi) = N(z) + p - eps*Tr(z*pi_bar)  (exact shift).

Plus: the public-geometry passport of every exposed PUBKEY_ONLY puzzle
(135/140/145/150/155/160), orbit checks included, and the 3/4 law tested on
the 160 verified solved keys.
"""
import csv
import os
import random
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))

random.seed(20260816)

p = 2**256 - 2**32 - 977
A_SP = 367917413016453100223835821029139468249
B_SP = 64502973549206556628585045361533709078
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
EXP3 = (p - 1) // 3
BETA1 = 0x851695d49a83f8ef919bb86153cbcb16630fb68aed0a766a3ec693d68e6afa40


def lift_uv(X):
    ku = (2 * X * (A_SP - B_SP) + p) // (2 * p)
    kv = (-2 * X * B_SP + p) // (2 * p)
    return X * (A_SP - B_SP) - ku * p, -X * B_SP - kv * p


def z_lift(X):
    u_num, v_num = lift_uv(X)
    ku = (X * (A_SP - B_SP) - u_num) // p
    kv = (-X * B_SP - v_num) // p
    return (X - ku * A_SP + kv * B_SP, -ku * B_SP - kv * (A_SP - B_SP))


def carry_c(X):
    z0, z1 = z_lift(X)
    w0, w1 = -z1, z0 - z1
    r0, r1 = z_lift(BETA * X % p)
    t0, t1 = w0 - r0, w1 - r1
    return (((A_SP - B_SP) * t0 + B_SP * t1) // p, (-B_SP * t0 + A_SP * t1) // p)


def s_num(X):
    u, v = lift_uv(X)
    return u * u - u * v + v * v


def om_mul(z):          # multiply by omega in standard coeffs
    return (-z[1], z[0] - z[1])


def ring_mul(a, b):     # (x0+y0 w)(x1+y1 w)
    return (a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0] - a[1]*b[1])


def trace(a):           # Tr(x + y w) = 2x - y
    return 2*a[0] - a[1]


PI_BAR = (A_SP - B_SP, -B_SP)   # conjugate of pi = a + b w  is  (a-b) - b w

print("=" * 88)
print(" GLV-ORBIT CARRY CONSERVATION -- THEOREM VERIFICATION")
print("=" * 88)

# ---- T1: closed form + exact 3-point law -----------------------------------
M = 100000
tally = {}
closed_form_ok = True
for _ in range(M):
    X = random.randrange(1, p)
    c = carry_c(X)
    tally[c] = tally.get(c, 0) + 1
    u_num, v_num = lift_uv(X)
    c_pred = (0, (2 * (u_num - v_num) + p) // (2 * p))
    if c != c_pred:
        closed_form_ok = False
print(f"T1  carry values observed: {sorted(tally)}")
print(f"    Pr[c=(0,0)]   = {tally.get((0,0),0)/M:.6f}   (exact 3/4  = 0.750000)")
print(f"    Pr[c=(0,1)]   = {tally.get((0,1),0)/M:.6f}   (exact 1/8  = 0.125000)")
print(f"    Pr[c=(0,-1)]  = {tally.get((0,-1),0)/M:.6f}  (exact 1/8  = 0.125000)")
print(f"    closed form c = (0, floor(u-v+1/2)) holds on all samples: {closed_form_ok}")

# ---- T2: orbit conservation + trichotomy -----------------------------------
N2 = 20000
cons_ok = trich_ok = True
for _ in range(N2):
    X = random.randrange(1, p)
    c1, c2, c3 = carry_c(X), carry_c(BETA * X % p), carry_c(BETA**2 % p * X % p)
    # omega^2 c1 + omega c2 + c3 = 0
    w2c1 = om_mul(om_mul(c1))
    wc2 = om_mul(c2)
    tot = (w2c1[0] + wc2[0] + c3[0], w2c1[1] + wc2[1] + c3[1])
    if tot != (0, 0):
        cons_ok = False
    if not (c1 == c2 == c3):
        trich_ok = False
print(f"T2  conservation w^2 c(X) + w c(bX) + c(b^2X) = 0: {cons_ok} ({N2} orbits)")
print(f"    trichotomy (all three carries EQUAL, orbit-invariant): {trich_ok}")

# ---- T3: norm orbit-invariance + exact shift formula ------------------------
N3 = 20000
inv_ok = shift_ok = True
n_c0 = 0
for _ in range(N3):
    X = random.randrange(1, p)
    c = carry_c(X)
    s0, s1 = s_num(X), s_num(BETA * X % p)
    if c == (0, 0):
        n_c0 += 1
        if not (s0 == s1 == s_num(BETA**2 % p * X % p)):
            inv_ok = False
    else:
        eps = 1 if c == (0, 1) else -1
        z = z_lift(X)
        # in N-units: N(z(bX)) = N(z) + p - eps*Tr(z pi_bar); s_num = p*N(z):
        rhs = s0 + p * p - eps * trace(ring_mul(z, PI_BAR)) * p
        if s1 != rhs:
            shift_ok = False
print(f"T3  c=0 => s(bX)=s(b^2X)=s(X) exactly: {inv_ok}  ({n_c0} of {N3} samples had c=0)")
print(f"    exact shift N(z(beX)) = N(z)+p-eps*Tr(z pi_bar): {shift_ok}")

# ---- passport of the exposed puzzles ----------------------------------------
print("\n PUBLIC-GEOMETRY PASSPORT (exposed PUBKEY_ONLY puzzles):")
master = {}
with open(os.path.join(_HERE, "btc_puzzle_master.csv")) as f:
    for row in csv.DictReader(f):
        if row["status"] == "PUBKEY_ONLY":
            master[int(row["puzzle"])] = (int(row["X_hex"], 16), int(row["Y_hex"], 16))
print(f" {'pz':>4} {'idx':>3} {'j':>2} {'y<p/2':>6} {'s':>12} {'gate':>5} {'c(X)':>7} "
      f"{'c(bX)':>7} {'c(b2X)':>7} {'s(bX)=s(X)':>10}")
for pz in sorted(master):
    x, y = master[pz]
    assert (y*y - x**3 - 7) % p == 0, f"P{pz} not on curve"
    h = pow(x, EXP3, p)
    e = {1: 0, BETA: 1, BETA1: 2}[h]
    sn = s_num(x)
    s = Fraction(sn, p * p)
    gate = 16 * sn < 3 * p * p
    c1 = carry_c(x)
    c2 = carry_c(BETA * x % p)
    c3 = carry_c(BETA**2 % p * x % p)
    print(f" {pz:>4} {e:>3} {(2*e)%3:>2} {str(2*y<p):>6} {float(s):>12.9f} "
          f"{str(gate):>5} {str(c1[1]):>7} {str(c2[1]):>7} {str(c3[1]):>7} "
          f"{str(s_num(BETA*x%p) == sn):>10}")

# ---- 3/4 law on the 160 verified solved keys --------------------------------
print("\n 3/4 LAW ON REAL SOLVED KEYS (puzzles_verified.csv):")
n = n0 = 0
cons_all = True
with open(os.path.join(_HERE, "puzzles_verified.csv")) as f:
    for row in csv.DictReader(f):
        X = int(row["X"], 16)
        c1 = carry_c(X)
        c2 = carry_c(BETA * X % p)
        c3 = carry_c(BETA**2 % p * X % p)
        n += 1
        if c1 == (0, 0):
            n0 += 1
        if not (c1 == c2 == c3):
            cons_all = False
print(f"    solved keys: {n}   c=0: {n0} ({100*n0/n:.1f}%)   nonzero: {n-n0}")
print(f"    expected 75.0% (binomial sd = {100*(0.75*0.25/n)**0.5:.1f}%)")
print(f"    orbit-conservation holds on all solved keys: {cons_all}")
print("=" * 88)
