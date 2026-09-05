#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
eis_nonequidist_followup_v1.py — resolve the flagged non-equidistribution of x([d]G) in the
Eisenstein torus (sessions d/g: core 0.771 vs 3/4, band-0 0.659 vs 0.680 at secp, N=20k, ~5-7 sigma).

Three decisive checks, exact integers in all signal paths:
  (1) CONVENTION: same x(dG) sample, three lift conventions — (a) mine (+-2 square-centering),
      (b) the project's canonical lift_uv (independent coordinate rounding, n16 script constants),
      (c) pure Babai coefficient rounding. If all agree -> convention ruled out.
  (2) SOURCE OF X at secp: x uniform in F_p (expect continuum rates) vs x = x([d]G)
      (expect the deformed rates). Isolates the QR-support conditioning at scale.
  (3) p-SCALING (exact, full enumeration): rates over ALL x in F_p vs over the SUPPORT
      {x: chi2(x^3+7) != -1}, p from 43 to ~1e5. Constant deformation -> real O(1) arithmetic
      signature reaching secp; decaying -> Weil-suppressed, secp flag suspect.
Floats only for rates/entropies (readout). No leakage claim (public marginal structure).
"""
import math, random, sys, os
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m40_n15_exact_accounting_v1 import Lift, legendre, qform

P_SECP = 2**256 - 2**32 - 977
N_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
A_SP = 367917413016453100223835821029139468249
B_SP = 64502973549206556628585045361533709078

def lift_project(X):
    """the project's canonical lift_uv (independent coordinate rounding) — n16 script verbatim."""
    p = P_SECP
    ku = (2 * X * (A_SP - B_SP) + p) // (2 * p)
    kv = (-2 * X * B_SP + p) // (2 * p)
    return X * (A_SP - B_SP) - ku * p, -X * B_SP - kv * p

def lift_babai(L_, X):
    """pure Babai coefficient rounding (no +-2 search)."""
    p = L_.p
    det = L_.b1[0] * L_.b2[1] - L_.b2[0] * L_.b1[1]
    r1 = round(Fraction(X * L_.b2[1], det))
    r2 = round(Fraction(-X * L_.b1[1], det))
    U = X - r1 * L_.b1[0] - r2 * L_.b2[0]
    V = - r1 * L_.b1[1] - r2 * L_.b2[1]
    return U, V

def rates_secp(lifted, label):
    """lifted = list of (U,V); report core/band rates vs continuum."""
    n0 = nc = 0
    for (U, V) in lifted:
        s = qform(U, V)
        n0 += (16 * s < 3 * P_SECP)
        nc += (4 * (U - V) ** 2 <= P_SECP)
    N = len(lifted)
    print(f"   {label:<44} band0 {n0/N:.4f} (0.6802)   core {nc/N:.4f} (0.7500)   N={N}")
    return n0 / N, nc / N

# ---- Jacobian EC on secp ----
def jac_double(P):
    if P is None: return None
    X, Y, Z = P
    if Y == 0: return None
    YY = Y * Y % P_SECP; S = 4 * X * YY % P_SECP; M = 3 * X * X % P_SECP
    X3 = (M * M - 2 * S) % P_SECP
    return (X3, (M * (S - X3) - 8 * YY * YY) % P_SECP, 2 * Y * Z % P_SECP)
def jac_add(P, Q):
    if P is None: return Q
    if Q is None: return P
    X1, Y1, Z1 = P; X2, Y2, Z2 = Q
    Z1Z1 = Z1 * Z1 % P_SECP; Z2Z2 = Z2 * Z2 % P_SECP
    U1 = X1 * Z2Z2 % P_SECP; U2 = X2 * Z1Z1 % P_SECP
    S1 = Y1 * Z2 % P_SECP * Z2Z2 % P_SECP; S2 = Y2 * Z1 % P_SECP * Z1Z1 % P_SECP
    H = (U2 - U1) % P_SECP; r = (S2 - S1) % P_SECP
    if H == 0: return jac_double(P) if r == 0 else None
    HH = H * H % P_SECP; HHH = H * HH % P_SECP; V = U1 * HH % P_SECP
    X3 = (r * r - HHH - 2 * V) % P_SECP
    return (X3, (r * (V - X3) - S1 * HHH) % P_SECP,
            ((Z1 + Z2) * (Z1 + Z2) - Z1Z1 - Z2Z2) % P_SECP * H % P_SECP)
def jac_mul(k, P):
    R = None
    while k:
        if k & 1: R = jac_add(R, P)
        P = jac_double(P); k >>= 1
    return R
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
     0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8, 1)

print("=" * 100)
print(" (1)+(2) secp, N=20000: convention x source-of-x — exact features, rates are readouts")
print("=" * 100)
L = Lift(P_SECP)
random.seed(20260821)
xs_curve = []
for _ in range(20000):
    d = random.randrange(1, N_SECP)
    Pn = jac_mul(d, G)
    zi = pow(Pn[2], P_SECP - 2, P_SECP); zi2 = zi * zi % P_SECP
    xs_curve.append(Pn[0] * zi2 % P_SECP)
xs_unif = [random.randrange(1, P_SECP) for _ in range(20000)]

lifted_a = [L.lift(x) for x in xs_curve]
lifted_b = [lift_project(x) for x in xs_curve]
lifted_c = [lift_babai(L, x) for x in xs_curve]
print(" CONVENTION (same x(dG) sample):")
rates_secp(lifted_a, "(a) mine: +-2 square-centering")
rates_secp(lifted_b, "(b) project lift_uv (coord rounding)")
rates_secp(lifted_c, "(c) pure Babai coefficient rounding")
print(" SOURCE OF X:")
rates_secp([L.lift(x) for x in xs_unif], "uniform x in F_p  (expect ~continuum)")
rates_secp(lifted_a, "x = x([d]G)             (the flagged sample)")

print()
print("=" * 100)
print(" (3) p-scaling: FULL enumeration, all-x vs QR-support-x rates (exact; continuum 0.6802/0.75)")
print("=" * 100)
print(f" {'p':>7} {'p%12':>5} | {'disk all':>9} {'disk sup':>9} {'dev':>8} | "
      f"{'core all':>9} {'core sup':>9} {'dev':>8}")
def scan_p(p):
    Lp = Lift(p)
    a_disk = a_core = s_disk = s_core = 0; na = ns = 0
    for x in range(p):
        U, V = Lp.lift(x)
        s = qform(U, V)
        disk = 16 * s < 3 * p
        core = 4 * (U - V) ** 2 <= p
        a_disk += disk; a_core += core; na += 1
        if legendre((x * x % p * x + 7) % p, p) != -1:
            s_disk += disk; s_core += core; ns += 1
    return a_disk / na, s_disk / ns, a_core / na, s_core / ns

def next_primes_1mod3(start, count):
    out = []
    c = start
    while len(out) < count:
        c += 1
        if c % 3 == 1 and all(c % f for f in range(2, int(c ** 0.5) + 1)):
            out.append(c)
    return out

plist = [43, 67, 79, 127, 163, 211, 349, 547, 823, 1051, 1303, 2003, 4001,
         10007, 20011, 50021, 100003]
devs_d = []; devs_c = []
for p in plist:
    ad, sd, ac, sc = scan_p(p)
    devs_d.append(sd - 0.6802); devs_c.append(sc - 0.75)
    print(f" {p:>7} {p%12:>5} | {ad:9.4f} {sd:9.4f} {sd-0.6802:+8.4f} | "
          f"{ac:9.4f} {sc:9.4f} {sc-0.75:+8.4f}")
print()
import statistics
# split-half trend: mean |dev| in the small half vs large half of the list
h = len(plist) // 2
print(f" |disk dev|: first half mean {statistics.fmean(abs(d) for d in devs_d[:h]):.4f} "
      f"vs second half {statistics.fmean(abs(d) for d in devs_d[h:]):.4f}")
print(f" |core dev|: first half mean {statistics.fmean(abs(d) for d in devs_c[:h]):.4f} "
      f"vs second half {statistics.fmean(abs(d) for d in devs_c[h:]):.4f}")
print(" (constant-ish => real O(1) signature reaching secp; shrinking ~p^-1/2 => Weil-suppressed)")
print("=" * 100)
