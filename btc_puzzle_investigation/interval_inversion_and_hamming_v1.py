#!/usr/bin/env python3
"""interval_inversion_and_hamming_v1.py -- the two covariates I dismissed, run properly.

WHY THIS EXISTS.  I dismissed the interval-inversion covariate as "no mechanism, near-zero prior".
That is a dismissal without object/class/power/scope -- the closure-by-declaration bar this project
explicitly forbids -- and it conflated LOW PRIOR with LOW POWER.  With M sampled d0 the test detects
correlation of order 1/sqrt(M); that is ordinary power.  So: run it.

OBJECT (in scope; the CONVERSION d -> [d]G, scalars constructed here).
  T(d0)  = sum_{i<W} chi_2(x_{[d0+i]G})        the incomplete sum at the 2^128 scale
  ARM A  (interval inversion) : does T(d0) track T(d0^{-1} mod N)?
           also the MACRO/spectral version the pointwise test cannot see: |T(d0)| vs |T(d0^{-1})|.
  ARM B  (Hamming weight)     : does T(d0) -- or |T(d0)| -- track popcount(d0)?
           NOTE popcount(d) IS a well-defined function of the group element (the binary expansion of
           d in [0,N) is unique), unlike (k1,k2).  Legal.  The motivation offered for it -- "double-
           and-add performs popcount(d) additions" -- is NOT a mechanism: [d]G is the same point for
           every multiplication algorithm, which is exactly why the Voronoi thesis died.  The test
           stands on its own as a well-posed question about d.

NULL.  Permute one side of the pairing (exact permutation p-values, integer counts).  This preserves
both marginals exactly and destroys only the pairing -- the thing under test.
CONTROLS.  C-PLANT on each arm: inject a coupling of known strength and confirm detection.

Exact integer arithmetic in the signal path.
"""

import random
import sys

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
A = 0
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8


def padd(Pt, Q):
    if Pt is None:
        return Q
    if Q is None:
        return Pt
    x1, y1 = Pt
    x2, y2 = Q
    if x1 == x2 and (y1 + y2) % P == 0:
        return None
    if Pt == Q:
        num, den = (3*x1*x1 + A) % P, (2*y1) % P
    else:
        num, den = (y2 - y1) % P, (x2 - x1) % P
    lm = num * pow(den, P - 2, P) % P
    x3 = (lm*lm - x1 - x2) % P
    return (x3, (lm*(x1 - x3) - y1) % P)


def pmul(d, Pt):
    R, Q = None, Pt
    while d:
        if d & 1:
            R = padd(R, Q)
        Q = padd(Q, Q)
        d >>= 1
    return R


def chi2(a):
    a %= P
    return 0 if a == 0 else (1 if pow(a, (P - 1)//2, P) == 1 else -1)


def T_of(d0, W, G):
    cur = pmul(d0 % N, G)
    s = 0
    for _ in range(W):
        s += chi2(cur[0])
        cur = padd(cur, G)
    return s


def perm_test(u, v, R, rng):
    """exact permutation p for the integer inner product sum(u_i v_i), pairing destroyed."""
    M = len(u)
    obs = sum(u[i]*v[i] for i in range(M))
    w = v[:]
    ge = 0
    for _ in range(R):
        rng.shuffle(w)
        if abs(sum(u[i]*w[i] for i in range(M))) >= abs(obs):
            ge += 1
    return obs, ge + 1, R + 1


def line(name, obs, a, b):
    print("      %-34s obs = %-12d exact perm p = %4d/%-5d %s"
          % (name, obs, a, b, "<-- FIRES" if a*20 <= b else ""))


if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    W = int(sys.argv[2]) if len(sys.argv) > 2 else 128
    R = 4000
    rng = random.Random(20260801)
    G = (Gx, Gy)

    print("=" * 96)
    print("ARM A: interval inversion   ARM B: Hamming weight   (M=%d intervals, W=%d, R=%d)"
          % (M, W, R))
    print("=" * 96)
    d0s = [rng.randrange(2**127, 2**128) for _ in range(M)]
    Td, Tinv, pc = [], [], []
    for j, d0 in enumerate(d0s):
        Td.append(T_of(d0, W, G))
        Tinv.append(T_of(pow(d0, N - 2, N), W, G))
        pc.append(bin(d0).count("1"))
        if (j + 1) % 25 == 0:
            print("   ... %d/%d" % (j + 1, M), flush=True)

    mpc = sum(pc)
    pcc = [x*M - mpc for x in pc]          # centred popcount, integer-exact (scaled by M)
    absTd = [abs(t) for t in Td]
    absTi = [abs(t) for t in Tinv]
    mad = sum(absTd)
    absTdc = [x*M - mad for x in absTd]

    print()
    print("   ARM A -- interval inversion")
    o, a, b = perm_test(Td, Tinv, R, rng)
    line("A1  T(d0) . T(d0^-1)", o, a, b)
    o, a, b = perm_test(absTdc, absTi, R, rng)
    line("A2  |T(d0)| . |T(d0^-1)|  (spectral)", o, a, b)

    print()
    print("   ARM B -- Hamming weight")
    o, a, b = perm_test(Td, pcc, R, rng)
    line("B1  T(d0) . popcount(d0)", o, a, b)
    o, a, b = perm_test(absTdc, pcc, R, rng)
    line("B2  |T(d0)| . popcount(d0)", o, a, b)

    print()
    print("   CONTROLS -- planted couplings of known strength (must fire)")
    for frac in (100, 50, 25, 12):
        k = M*frac//100
        planted = Tinv[:]
        idx = list(range(M))
        rng.shuffle(idx)
        for i in idx[:k]:
            planted[i] = Td[i]                      # force exact agreement on a fraction
        o, a, b = perm_test(Td, planted, R, rng)
        line("C-PLANT A  %3d%% of pairs forced" % frac, o, a, b)
    for frac in (100, 50, 25, 12):
        k = M*frac//100
        planted = pcc[:]
        idx = list(range(M))
        rng.shuffle(idx)
        for i in idx[:k]:
            planted[i] = Td[i]*abs(pcc[i] if pcc[i] else 1)
        o, a, b = perm_test(Td, planted, R, rng)
        line("C-PLANT B  %3d%% of pairs forced" % frac, o, a, b)

    print()
    print("   spread check: T(d0) ranges %d..%d ; popcount ranges %d..%d"
          % (min(Td), max(Td), min(pc), max(pc)))
