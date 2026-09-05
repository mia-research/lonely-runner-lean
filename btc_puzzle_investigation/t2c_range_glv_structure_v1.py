#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
t2c_range_glv_structure_v1.py — is T2c a dead 'redundant-or-gated' dichotomy, or live?

Tests, exactly, what the PUBLIC range d in [2^(k-1), 2^k) does to the GLV halves
(a,b)=glv(d) and to the carry eps=fn(a,b). This is a DETERMINISTIC computation on
known d (no secret, no leakage null): it maps the PUBLIC constraint through the
PUBLIC GLV map. It decides whether:
  (i)  the range confines (a,b) to a strip strictly inside the full ~sqrt(n) box
       (=> a range-restricted 2-D search region, NOT the full 2-D DLP), and
  (ii) eps is CONSTANT on the range (redundant) or VARIES (a real bit within a
       bounded region).
Exact integers only.
"""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ecc_secp256k1 import N_ORDER

LAM = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72

def _rdiv(nu, de):
    if de < 0: nu, de = -nu, -de
    q, r = divmod(nu, de); return q + 1 if 2*r >= de else q
def _dot(u, v): return u[0]*v[0] + u[1]*v[1]
def _gauss(u, v):
    while True:
        if _dot(v, v) < _dot(u, u): u, v = v, u
        m = _rdiv(_dot(u, v), _dot(u, u)); v = (v[0]-m*u[0], v[1]-m*u[1])
        if _dot(v, v) >= _dot(u, u): return u, v
GB1, GB2 = _gauss((N_ORDER, 0), (-LAM, 1))
GDET = GB1[0]*GB2[1] - GB1[1]*GB2[0]
def glv(d):
    c1 = _rdiv(d*GB2[1], GDET); c2 = _rdiv(-d*GB1[1], GDET)
    return d - (c1*GB1[0]+c2*GB2[0]), -(c1*GB1[1]+c2*GB2[1])
def eps(d):
    a, b = glv(d); return int((a % N_ORDER) + (b % N_ORDER) >= N_ORDER)

SQRTN_BITS = (N_ORDER.bit_length() + 1)//2      # ~128
print("="*88)
print(f" T2c: what the public range does to GLV halves + carry   (sqrt(n) ~ 2^{SQRTN_BITS})")
print("="*88)
random.seed(20260818)
M = 40000
for k in [40, 129, 135, 160, 200, 255]:
    lo, hi = 2**(k-1), 2**k
    amax = bmax = 0; amin = bmin = None; ones = 0
    span = min(M, hi-lo)
    for _ in range(span):
        d = random.randrange(lo, hi)
        a, b = glv(d)
        amax = max(amax, abs(a)); bmax = max(bmax, abs(b))
        amin = abs(a) if amin is None else min(amin, abs(a))
        bmin = abs(b) if bmin is None else min(bmin, abs(b))
        ones += eps(d)
    ab_bits = max(amax, bmax).bit_length()
    # crude "area fraction" of the (a,b) box the range covers, in bits
    box_bits = 2*SQRTN_BITS
    used_bits = amax.bit_length() + bmax.bit_length()
    print(f"  k={k:3d} (range 2^{k-1}..2^{k}, n_samp={span}): "
          f"max|a,b| ~ 2^{ab_bits:3d} | min|a| 2^{(amin or 1).bit_length()}, "
          f"min|b| 2^{(bmin or 1).bit_length()} | eps ones {ones}/{span} = {ones/span:.3f}")
print("-"*88)
print(" reference: FULL range d in [1,n)  -> eps ones ~ 0.500 (balanced), max|a,b| ~ 2^128")
print("="*88)
