#!/usr/bin/env python3
"""AUDIT_shortscalar_glv_interval_harness_v1.py -- instrument audit of the proposed 2^128 harness.

Checks, in order of severity:
  A1  GLV correctness: does k1 + k2*LAMBDA = d (mod N)?  Are k1,k2 actually SHORT (~2^128)?
      The proposal uses FLOOR division (`//`) where Babai rounding needs ROUND-TO-NEAREST.
  A2  Does the feature N(kappa) VARY across a short interval at 2^128, or is it effectively
      constant?  (c1 = round(d*B2/N) changes by ~width*2^128/2^256 across the interval.)
  A3  Is the statistic dominated by a PERMUTATION-INVARIANT term?  A free shuffle preserves
      sum(readouts); if N is near-constant then S ~ N0 * sum(readouts) is the SAME for every
      permutation, and the test has no power by construction.
  A4  C-PLANT: inject a perfect coupling and see whether the proposed test detects it.
      A test that cannot see a planted signal cannot see a real one.

Exact integer arithmetic in the signal path.
"""

import random

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
A = 0
B = 7
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
LAMBDA = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72

A1 = 0x3086D221A7D46BCDE86C90E49284EB15
B1 = -0xE4437ED6010E88286F547FA90ABFE4C3
A2 = 0x114CA50F7A8E2F3F657C1108D9D44CFD8
B2 = 0x3086D221A7D46BCDE86C90E49284EB15


def legendre(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p - 1)//2, p) == 1 else -1)


def point_add(P1, P2):
    if P1 is None:
        return P2
    if P2 is None:
        return P1
    x1, y1 = P1
    x2, y2 = P2
    if x1 == x2 and (y1 + y2) % P == 0:
        return None
    if P1 == P2:
        num, den = (3*x1*x1 + A) % P, (2*y1) % P
    else:
        num, den = (y2 - y1) % P, (x2 - x1) % P
    lam = num * pow(den, P - 2, P) % P
    x3 = (lam*lam - x1 - x2) % P
    return (x3, (lam*(x1 - x3) - y1) % P)


def point_mul(d, pt):
    R0, R1 = None, pt
    for i in range(255, -1, -1):
        if (d >> i) & 1:
            R0 = point_add(R0, R1)
            R1 = point_add(R1, R1)
        else:
            R1 = point_add(R0, R1)
            R0 = point_add(R0, R0)
    return R0


def rnd_div(a, b):
    """round-to-nearest integer division, exact, b > 0."""
    q, r = divmod(a, b)
    return q + 1 if 2*r >= b else q


def glv_floor(d):
    """the PROPOSAL's version: floor division."""
    c1 = (d * B2) // N
    c2 = -(d * B1) // N
    k1 = d - c1*A1 - c2*A2
    k2 = -c1*B1 - c2*B2
    return k1, k2


def glv_round(d):
    """Babai rounding done correctly: round-to-nearest."""
    c1 = rnd_div(d * B2, N)
    c2 = rnd_div(-(d * B1), N)
    k1 = d - c1*A1 - c2*A2
    k2 = -c1*B1 - c2*B2
    return k1, k2


def norm(k1, k2):
    return k1*k1 - k1*k2 + k2*k2


def bits(x):
    return abs(x).bit_length()


print("=" * 90)
print("A1 -- GLV CORRECTNESS AND SHORTNESS  (floor vs round-to-nearest)")
print("=" * 90)
rng = random.Random(1)
for label, fn in (("FLOOR (as proposed)", glv_floor), ("ROUND (correct Babai)", glv_round)):
    okmod = True
    maxb = 0
    for _ in range(200):
        d = rng.randrange(1, N)
        k1, k2 = fn(d)
        if (k1 + k2*LAMBDA - d) % N != 0:
            okmod = False
        maxb = max(maxb, bits(k1), bits(k2))
    print("  %-22s | k1 + k2*LAMBDA = d (mod N): %-5s | max bit-length of k1,k2: %d"
          % (label, okmod, maxb))
print("  (a genuine GLV lift has |k1|,|k2| ~ 2^128, i.e. bit-length <= ~129)")

print()
print("=" * 90)
print("A2 -- DOES THE FEATURE VARY ACROSS A SHORT INTERVAL AT 2^128?")
print("=" * 90)
start = 2**128
width = 1000
for label, fn in (("FLOOR (as proposed)", glv_floor), ("ROUND (correct)", glv_round)):
    k1s, k2s, ns = [], [], []
    for i in range(width):
        k1, k2 = fn(start + i)
        k1s.append(k1)
        k2s.append(k2)
        ns.append(norm(k1, k2))
    k2_const = len(set(k2s)) == 1
    k1_lin = all(k1s[i+1] - k1s[i] == 1 for i in range(width - 1))
    nmin, nmax = min(ns), max(ns)
    spread = nmax - nmin
    print("  %-22s | k2 constant over interval: %-5s | k1 increments by exactly 1: %-5s"
          % (label, k2_const, k1_lin))
    print("  %-22s | N ~ 2^%d, spread across interval ~ 2^%d  => relative variation ~ 2^-%d"
          % ("", bits(nmax), bits(spread), bits(nmax) - bits(spread)))

print()
print("=" * 90)
print("A3 -- IS THE STATISTIC DOMINATED BY A PERMUTATION-INVARIANT TERM?")
print("=" * 90)
print("  A free shuffle preserves sum(readouts) = T.  Writing N_i = N0 + delta_i,")
print("      S = sum r_i N_i = N0*T + sum r_i delta_i,")
print("  the first term is IDENTICAL for every permutation.  Only the delta term moves.")
k1s = [glv_round(start + i) for i in range(width)]
ns = [norm(a, b) for (a, b) in k1s]
N0 = min(ns)
deltas = [v - N0 for v in ns]
print("  N0 ~ 2^%d | max delta ~ 2^%d | the permutation can only move the statistic by a")
print("  relative ~2^-%d of its own size." % (bits(N0) - bits(max(deltas))))
print("  Printed: N0 bits = %d, max delta bits = %d" % (bits(N0), bits(max(deltas))))

print()
print("=" * 90)
print("A4 -- C-PLANT: can the proposed test detect a PERFECT planted coupling?")
print("=" * 90)
print("  Building the real interval at 2^128 (1000 scalars, exact curve arithmetic)...")
cur = point_mul(start, (Gx, Gy))
readouts = []
for i in range(width):
    readouts.append(legendre(cur[0], P))
    cur = point_add(cur, (Gx, Gy))
print("  ...done. readout balance: +1 x %d, -1 x %d"
      % (readouts.count(1), readouts.count(-1)))


def proposed_test(readouts, norms, R=2000, seed=12345):
    rng = random.Random(seed)
    S = sum(readouts[i]*norms[i] for i in range(len(norms)))
    ge = 0
    for _ in range(R):
        q = readouts[:]
        rng.shuffle(q)
        if abs(sum(q[i]*norms[i] for i in range(len(norms)))) >= abs(S):
            ge += 1
    return S, ge, R


S, ge, R = proposed_test(readouts, ns)
print("  REAL DATA     : p = %d/%d" % (ge + 1, R + 1))

med = sorted(ns)[len(ns)//2]
planted = [1 if ns[i] > med else -1 for i in range(width)]
S2, ge2, R2 = proposed_test(planted, ns)
print("  PERFECT PLANT : readout := sign(N - median(N)), i.e. a 100%% coupling")
print("                  p = %d/%d   %s"
      % (ge2 + 1, R2 + 1,
         "FIRES" if (ge2 + 1)*20 <= (R2 + 1) else "*** DOES NOT FIRE -- test has no power ***"))

anti = [-v for v in planted]
S3, ge3, R3 = proposed_test(anti, ns)
print("  ANTI-PLANT    : p = %d/%d" % (ge3 + 1, R3 + 1))

rand = [1 if random.Random(99).random() < 0.5 else -1 for _ in range(width)]  # noqa: float
S4, ge4, R4 = proposed_test(rand, ns)
print("  PURE NOISE    : p = %d/%d" % (ge4 + 1, R4 + 1))
print()
print("  If PERFECT PLANT and PURE NOISE give the same p-value, the test is measuring nothing")
print("  about the data -- it is reporting the permutation-invariance of N0*T.")
