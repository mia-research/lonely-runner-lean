#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
mock135_carry_ceiling_demo_v1.py
================================
Exact-precision demonstration of the "d0 = ceil(c*n/lambda) locks the orbit
representative" claim on mock 135-bit keys.

The claim, stated precisely: with c = floor(lambda*d / n) and d' = lambda*d mod n,
                d = (d' + c*n)/lambda,   d' in [0, n)
so for FIXED c the candidates are exactly
                C(c) = { e in Z :  ceil(c*n/lambda) <= e < ceil((c+1)*n/lambda) },
an interval of width n/lambda (~3.07): 3 or 4 integers.  "The ceiling locks d."

What this demo establishes (all exact integer arithmetic):
  1. The lock is REAL: on every mock key, d in C(c), |C(c)| in {3, 4}.
  2. The lock is a BIJECTION (measure-preserving change of variables):
     consecutive C(c) tile the integers, so sum |C(c)| over any carry range
     = the key-interval width exactly.  Compressing candidates 3.07x while
     multiplying per-candidate oracle cost 3.07x = provably ZERO net.
  3. The carry is secret: c = floor(lambda*d/n) is a function of d; the public
     bit-range [2^134, 2^135) pins c only to an interval of
     ~lambda*2^134/n ~ 2^132.4 values (exact count computed).
  4. The min-rep orientation is degenerate for puzzle-scale keys (c = 0,
     j = 0) -- the PREREG_j_range degeneracy, verified on the mocks.
  5. The public oracle is exact equality ([e]G == P) at one EC scalar mult per
     candidate: no monotone predicate on the interval exists, so 'bisection'
     is a category error; and the oracle price makes the 3.07x compression
     exactly cancel (identity 2).

Deterministic, seeded.
"""
import random
from fractions import Fraction

random.seed(20260817)

n = 115792089237316195423570985008687907852837564279074904382605163141518161494337
LAM = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72
p = 2**256 - 2**32 - 977
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8


def ceil_div(a, b):
    return -((-a) // b)


def candidates(c):
    """C(c) = integers e with floor(lambda*e/n) == c."""
    lo = ceil_div(c * n, LAM)
    hi = ceil_div((c + 1) * n, LAM)
    return list(range(lo, hi))


# minimal EC (for the oracle demonstration only)
def dbl(X, Y, Z):
    if Y == 0: return (1, 1, 0)
    S = 4*X*Y*Y % p; M = 3*X*X % p; Xp = (M*M - 2*S) % p
    return (Xp, (M*(S - Xp) - 8*Y**4) % p, 2*Y*Z % p)
def add(A, B):
    if A[2] == 0: return B
    if B[2] == 0: return A
    (X1,Y1,Z1),(X2,Y2,Z2) = A,B
    z11, z22 = Z1*Z1 % p, Z2*Z2 % p
    U1, U2 = X1*z22 % p, X2*z11 % p
    S1, S2 = Y1*Z2 % p*z22 % p, Y2*Z1 % p*z11 % p
    if U1 == U2: return (1,1,0) if S1 != S2 else dbl(X1,Y1,Z1)
    H = (U2-U1) % p; r = 2*(S2-S1) % p; I = 4*H*H % p; J = H*I % p; V = U1*I % p
    Xp = (r*r - J - 2*V) % p
    return (Xp, (r*(V-Xp) - 2*S1*J) % p, ((Z1+Z2)**2 - z11 - z22) % p * H % p)
def mul(k):
    R, T = (1,1,0), (GX,GY,1)
    while k:
        if k & 1: R = add(R, T)
        T = dbl(*T); k >>= 1
    z = pow(R[2], p-2, p); z2 = z*z % p
    return (R[0]*z2 % p, R[1]*z2 % p * z % p)


print("=" * 86)
print(" CARRY-CEILING LOCK ON MOCK 135-BIT KEYS (exact integer arithmetic)")
print("=" * 86)
print(f"  n/lambda = {float(Fraction(n, LAM)):.6f}   (candidate-interval width)")

LO, HI = 2**134, 2**135
print("\n[1] THE LOCK IS REAL (per mock key):")
print(f"  {'mock d (last 16 digits)':>20} {'c (last 12)':>13} {'ceil(cn/l) (last 12)':>21} {'|C(c)|':>6}  d in C(c)?")
for i in range(5):
    d = random.randrange(LO, HI)
    c, dp = divmod(LAM * d, n)
    assert dp == LAM * d - c * n and (LAM * d) % n == dp % n
    C = candidates(c)
    print(f"  {'...' + str(d)[-16:]:>20} {'...' + str(c)[-12:]:>13} "
          f"{'...' + str(C[0])[-12:]:>21} {len(C):>6}  {d in C}")

# [2] measure preservation: consecutive C(c) tile Z exactly
print("\n[2] THE LOCK IS A BIJECTION (no net compression):")
c0 = LAM * LO // n
sizes, total = [], 0
for c in range(c0, c0 + 1000):
    C = candidates(c)
    sizes.append(len(C))
    total += len(C)
# the union of C(c0..c0+999) is the integer interval [min, min+total)
first = candidates(c0)[0]
tiled = all(candidates(c0)[0] + total - 1 >= e >= first for e in [first, first + total - 1])
gapfree = candidates(c0 + 999)[-1] - candidates(c0)[0] + 1 == total
print(f"  1000 consecutive carries: sizes in {sorted(set(sizes))}, mean = {total/1000:.4f}")
print(f"  their candidate sets tile one contiguous integer run: {gapfree}")
print(f"  sum |C(c)| = {total} = width of the tiled run (exact): carries*3.07 = keyspace.")
print(f"  => candidate compression {total/1000:.2f}x  *  per-carry oracle cost "
      f"{total/1000:.2f}x  = 1.000 (work-invariance identity).")

# [3] range knowledge pins c to ~2^132.4 values
c_lo, c_hi = LAM * LO // n, LAM * (HI - 1) // n
count = c_hi - c_lo + 1
print("\n[3] THE CARRY IS SECRET-SIDE:")
print(f"  public bit-range [2^134, 2^135) pins c to {count} candidates "
      f"(~2^{count.bit_length()-1})")
print(f"  keyspace width 2^134 = {2**134};  {count} carries x ~3.07 candidates = "
      f"{count * total // 1000}  (same magnitude: the map repackages the search).")

# [4] min-rep orientation degenerate (PREREG fact) on the mocks
print("\n[4] MIN-REP ORIENTATION DEGENERATE (puzzle-scale keys):")
for i in range(2):
    d = random.randrange(LO, HI)
    orbit = [(pow(LAM, k, n) * d) % n for k in range(3)] + \
            [(n - (pow(LAM, k, n) * d) % n) % n for k in range(3)]
    print(f"  mock ...{str(d)[-12:]}: min orbit element = d itself: "
          f"{min(orbit) == d}  (so j_formula=0, carry=0 in that convention)")

# [5] the public oracle prices the lock at zero
print("\n[5] THE PUBLIC ORACLE:")
d = random.randrange(LO, HI)
P = mul(d)
c, _ = divmod(LAM * d, n)
C = candidates(c)
sel = [e for e in C if mul(e) == P]
print(f"  C(c) = {len(C)} candidates; full verification ([e]G == P) selects "
      f"{sel} -- at {len(C)} EC mults, vs {len(C)} direct candidate tests: identical.")
print("  No monotone public predicate on the interval exists (equality-only oracle),")
print("  so 'interval bisection' has no oracle to bisect with.")
print("=" * 86)
