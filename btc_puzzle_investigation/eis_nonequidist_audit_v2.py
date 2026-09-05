#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
eis_nonequidist_audit_v2.py — audit of NOTE_eis_nonequidist_resolved_v1: the v1 canonical check
covered ONLY the core predicate at N=20k. This closes the gap:
  Part 1 (secp, N=200 000): the PROJECT-CANONICAL machinery (int1_frame_operator_v1.build_secp:
  eis + eps) on curve-x vs uniform-x — full 3-class eps rates AND the s<3/16 rate via exact
  16*enorm(eis(X)) < 3p. Power: sigma ~ 0.0015 per rate (resolves >=0.3% effects).
  Part 2 (generic build(p), FULL enumeration): all-x vs QR-support-x rates of eps==0 and s<3/16
  at p = 43, 163, 547, 1303, 20011, 100003 — the Weil-decay check redone canonically.
Exact integers in all signal paths; floats only for rates.
"""
import math, random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from int1_frame_operator_v1 import build, build_secp
from lift_sextant_rhombus_law_proof_v2 import enorm

P = 2**256 - 2**32 - 977
N_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def jac_double(Pt):
    if Pt is None: return None
    X, Y, Z = Pt
    if Y == 0: return None
    YY = Y * Y % P; S = 4 * X * YY % P; M = 3 * X * X % P
    X3 = (M * M - 2 * S) % P
    return (X3, (M * (S - X3) - 8 * YY * YY) % P, 2 * Y * Z % P)
def jac_add(Pt, Qt):
    if Pt is None: return Qt
    if Qt is None: return Pt
    X1, Y1, Z1 = Pt; X2, Y2, Z2 = Qt
    Z1Z1 = Z1 * Z1 % P; Z2Z2 = Z2 * Z2 % P
    U1 = X1 * Z2Z2 % P; U2 = X2 * Z1Z1 % P
    S1 = Y1 * Z2 % P * Z2Z2 % P; S2 = Y2 * Z1 % P * Z1Z1 % P
    H = (U2 - U1) % P; r = (S2 - S1) % P
    if H == 0: return jac_double(Pt) if r == 0 else None
    HH = H * H % P; HHH = H * HH % P; V = U1 * HH % P
    X3 = (r * r - HHH - 2 * V) % P
    return (X3, (r * (V - X3) - S1 * HHH) % P,
            ((Z1 + Z2) * (Z1 + Z2) - Z1Z1 - Z2Z2) % P * H % P)
def jac_mul(k, Pt):
    R = None
    while k:
        if k & 1: R = jac_add(R, Pt)
        Pt = jac_double(Pt); k >>= 1
    return R
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
     0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8, 1)

M = 200_000
print("=" * 104)
print(f" Part 1 — secp, canonical machinery (build_secp eis/eps), N={M} per source", flush=True)
print("=" * 104)
eis, eps = build_secp()

random.seed(20260822)
xs_curve = []
for _ in range(M):
    d = random.randrange(1, N_ORDER)
    Pn = jac_mul(d, G)
    zi = pow(Pn[2], P - 2, P); zi2 = zi * zi % P
    xs_curve.append(Pn[0] * zi2 % P)
xs_unif = [random.randrange(1, P) for _ in range(M)]
print(f" [x samples generated]", flush=True)

def stats(xs, label):
    c0 = c1 = c2 = sd = sq = 0
    for X in xs:
        e = eps(X)
        if e == 0: c0 += 1
        elif e == 1: c1 += 1
        else: c2 += 1
        w = eis(X)
        en = enorm(w)
        sd += (16 * en < 3 * P)
        sq += (4 * en < P)
    N = len(xs)
    print(f"   {label:<28} eps0 {c0/N:.5f} (0.75)  eps+ {c1/N:.5f}  eps- {c2/N:.5f} (0.125)  "
          f"s<3/16 {sd/N:.5f} (0.68017)  s<1/4 {sq/N:.5f}", flush=True)
    return c0 / N, c1 / N, c2 / N, sd / N, sq / N

ru = stats(xs_unif, "uniform x in F_p")
rc = stats(xs_curve, "x = x([d]G)")
N = M
print("   deltas (curve - uniform) with z:")
for i, (nm, cont) in enumerate([("eps0", 0.75), ("eps+", 0.125), ("eps-", 0.125),
                                ("s<3/16", 0.68017), ("s<1/4", None)]):
    du, dc = ru[i], rc[i]
    r = (du + dc) / 2
    sig = math.sqrt(2 * r * (1 - r) / N)
    print(f"     {nm:<8} uniform {du:.5f} curve {dc:.5f}  delta {dc - du:+.5f}  "
          f"({abs(dc - du) / sig if sig else 0:.2f} sigma)", flush=True)

print()
print("=" * 104)
print(" Part 2 — canonical scaling: FULL enumeration, all-x vs QR-support-x (generic build(p))")
print("=" * 104)
def legendre_(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1
print(f" {'p':>7} | {'eps0 all':>9} {'eps0 sup':>9} {'dev':>8} | {'disk all':>9} {'disk sup':>9} {'dev':>8}")
for p in (43, 163, 547, 1303, 20011, 100003):
    eisp, epsp = build(p)
    a0 = as0 = ad = asd = 0; na = ns = 0
    for X in range(p):
        e = epsp(X); w = eisp(X); en = enorm(w)
        z0 = (e == 0); zd = (16 * en < 3 * p)
        a0 += z0; ad += zd; na += 1
        if legendre_((X * X % p * X + 7) % p, p) != -1:
            as0 += z0; asd += zd; ns += 1
    print(f" {p:>7} | {a0/na:9.5f} {as0/ns:9.5f} {as0/ns-a0/na:+8.5f} | "
          f"{ad/na:9.5f} {asd/ns:9.5f} {asd/ns-ad/na:+8.5f}", flush=True)
print(" (sup-minus-all deviation decaying ~p^-1/2 => Weil-suppressed; constant => real O(1) effect)")
print("=" * 104)
