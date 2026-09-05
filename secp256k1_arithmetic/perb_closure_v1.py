#!/usr/bin/env python3
"""
Per-b amicable closure constants rho_b for y^2 = x^3 + b, b = 1..8 (2026-07-11).

For each b:
  1. find the single-symbol formula u_b = u0 * (c/pi)_6^e (search as in P1),
     training on split ell < 1500, validating on 1500..4000;
  2. verify u_b is a class function of the primary Frobenius mod M (smallest
     M in {12b, 24b, 48b} with zero violations over split ell < 3*10^5);
  3. exact census: rho_b = fraction of allowed classes (pi and pi-1 coprime
     to the bad primes) that close the 2-cycle;
  4. empirical: closure rate and unordered amicable-pair count for ell < 15000
     by BRUTE POINT COUNTS (no formula), as ground truth.

Falsification: ordering/ratios of rho_b must match the brute pair counts;
b = 1, 8 (2-torsion) and b = 1, 4 (3-torsion) must give zero allowed classes.
"""

import math

UNITS = [(1,0), (-1,0), (0,1), (0,-1), (-1,-1), (1,1)]
IDX2POW = {0:0, 1:3, 2:2, 3:5, 4:4, 5:1}
POW2IDX = {v:k for k,v in IDX2POW.items()}

def mulw(a, b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def Nrm(v): return v[0]*v[0]-v[0]*v[1]+v[1]*v[1]
def Tr(v):  return 2*v[0]-v[1]
def conj(v): return (v[0]-v[1], -v[1])
def uinv(i): return POW2IDX[(-IDX2POW[i]) % 6]

def primary(v):
    hits = [(i, mulw(u, v)) for i, u in enumerate(UNITS)
            if (u[0]*v[0]-u[1]*v[1]) % 3 == 2 and (u[0]*v[1]+u[1]*v[0]-u[1]*v[1]) % 3 == 0]
    assert len(hits) == 1
    return hits[0]

def cornacchia(ell):
    for y in range(1, math.isqrt(4*ell//3)+2):
        d = 4*ell - 3*y*y
        if d < 0: break
        s = math.isqrt(d)
        if s*s == d and (s+y) % 2 == 0: return ((s+y)//2, y)

def sieve(limit):
    bs = bytearray([1])*(limit+1); bs[0:2] = b'\x00\x00'
    for i in range(2, math.isqrt(limit)+1):
        if bs[i]: bs[i*i::i] = bytearray(len(bs[i*i::i]))
    return bs

LIMS = 300_000
BS = sieve(LIMS)
PRIMES = [i for i in range(LIMS+1) if BS[i]]
SPLITS = [r for r in PRIMES if r % 3 == 1 and r > 3]

def a_count(ell, b):
    qr = bytearray(ell)
    for x in range((ell//2)+1): qr[x*x % ell] = 1
    c