#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
m40_n15_addendum_decomp_secp_v1.py — (1) decompose the A4 pairwise MI into its forced anti-diagonal
contribution vs the rest (is the group-law coupling on M40's forced subspace anything beyond the
trivial d1+d2=0 forcing?); (2) secp-scale tuple budget (exact features, sampled d).
"""
import math, random, sys, os
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m40_n15_exact_accounting_v1 import curve_walk, Lift, readouts, legendre, H_bits

print("=" * 100)
print(" (1) A4 MI decomposition: anti-diagonal (d1+d2=0) forced part vs the rest — exact")
print("=" * 100)
for p in (43, 67, 79, 127, 163, 211, 349, 61):
    n, h, xs = curve_walk(p)
    leg = 1 if p % 4 == 1 else -1
    # full MI restricted to s != 0  (drop the forced-zero rows entirely)
    c_joint = Counter(); c_s = Counter(); c_p = Counter()
    N2 = 0
    for d1 in range(1, n):
        f1 = h[d1]
        for d2 in range(1, n):
            s = (d1 + d2) % n
            if s == 0:
                continue                     # the forced anti-diagonal
            fs = h[s]; f2 = h[d2]
            c_joint[(fs, f1, f2)] += 1; c_s[fs] += 1; c_p[(f1, f2)] += 1; N2 += 1
    MI_off = 0.0
    for (fs, f1, f2), c in c_joint.items():
        MI_off += c / N2 * math.log2((c * N2) / (c_s[fs] * c_p[(f1, f2)]))
    # diagonal d1 == d2 (s = 2d1) contribution for reference
    print(f"  p={p:>3} n={n:>3}: MI off the anti-diagonal (s!=0, all {N2} pairs) = {MI_off:.6f} bits"
          f"  [{'FLAT' if MI_off < 5e-3 else 'NONZERO'}; scale 1/n = {1/n:.6f}]")

print()
print("=" * 100)
print(" (2) secp-scale tuple budget (exact features on [d]G, d sampled; descriptive rates)")
print("=" * 100)
p = 2**256 - 2**32 - 977
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
# Jacobian arithmetic (a=0, b=7)
def jac_double(P):
    if P is None: return None
    X, Y, Z = P
    if Y == 0: return None
    YY = Y*Y % p; S = 4*X*YY % p; M = 3*X*X % p
    return ((M*M - 2*S) % p, (M*(S - (M*M - 2*S)) - 8*YY*YY) % p, 2*Y*Z % p)
def jac_add(P, Q):
    if P is None: return Q
    if Q is None: return P
    X1,Y1,Z1 = P; X2,Y2,Z2 = Q
    Z1Z1 = Z1*Z1 % p; Z2Z2 = Z2*Z2 % p
    U1 = X1*Z2Z2 % p; U2 = X2*Z1Z1 % p
    S1 = Y1*Z2 % p * Z2Z2 % p; S2 = Y2*Z1 % p * Z1Z1 % p
    H = (U2 - U1) % p; r = (S2 - S1) % p
    if H == 0:
        return jac_double(P) if r == 0 else None
    HH = H*H % p; HHH = H*HH % p; V = U1*HH % p
    X3 = (r*r - HHH - 2*V) % p
    return (X3, (r*(V - X3) - S1*HHH) % p, ((Z1+Z2)*(Z1+Z2) - Z1Z1 - Z2Z2) % p * H % p)
def jac_mul(k, P):
    R = None
    while k:
        if k & 1: R = jac_add(R, P)
        P = jac_double(P); k >>= 1
    return R
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
     0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8, 1)
L = Lift(p)
random.seed(20260821)
M = 20000
ce = Counter(); cs = Counter(); cb = Counter(); cf = Counter(); call = Counter()
for _ in range(M):
    d = random.randrange(1, n)
    Pn = jac_mul(d, G)
    zi = pow(Pn[2], p - 2, p); zi2 = zi * zi % p
    x = Pn[0] * zi2 % p; y = Pn[1] * zi2 % p * zi % p
    U, V = L.lift(x)
    e, sext, band = readouts(U, V, p)
    f_ = 1 if pow(y, (p - 1) // 2, p) == 1 else -1
    ce[e] += 1; cs[sext] += 1; cb[band] += 1; cf[f_] += 1
    call[(e, sext, band, f_)] += 1
He, Hs, Hb, Hf = H_bits(ce, M), H_bits(cs, M), H_bits(cb, M), H_bits(cf, M)
Hall = H_bits(call, M)
print(f"  N={M} random d at secp:  H(e)={He:.4f} (Cap-Law 0.811)  H(sext)={Hs:.4f} (max 2.585)  "
      f"H(band)={Hb:.4f}  H(f)={Hf:.4f}")
print(f"  TUPLE H = {Hall:.4f} bits | sum of marginals = {He+Hs+Hb+Hf:.4f} | "
      f"synergy = {Hall-(He+Hs+Hb+Hf):+.4f}")
sizes = [c for c in call.values()]
print(f"  occupied cells {len(call)}/{3*6*3*2}; empirical class rates: "
      f"e: {sorted(ce.items())}")
print(f"  band: {sorted(cb.items())} | f: {sorted(cf.items())}")
