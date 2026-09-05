#!/usr/bin/env python3
"""pointwise_inversion_2p128_item5_v1.py -- ITEM 5: the pointwise inversion statistic at 2^128.

OBJECT.   S = sum_i a_i b_i,  a_i = chi_2(x_{[d_i]G}),  b_i = chi_2(x_{[d_i^{-1}]G}),
          d_i drawn from a dyadic interval [2^(k-1), 2^k).
          d -> d^{-1} mod n is the NON-ALGEBRAIC index map that survives the Weil closure
          (STRUCTURAL_IMPLICATIONS Sec 5.3); the record settled it only at p ~ 10^4, never at 2^128.

STRUCTURAL CONSTRAINTS INTERROGATED BEFORE ANY MEASUREMENT
  (1) x(-d) = x(d)             => a is EVEN in d; and (-d)^{-1} = -(d^{-1}) so b is even too.
                                  The summand is EVEN: pairing d <-> -d gives 2x, NOT 0.  Not annihilated.
  (2) x(lambda d) = beta x_d   => chi_2(beta) = 1 so a is mu_3-INVARIANT; and (lambda d)^{-1} =
                                  lambda^2 d^{-1}, so b is too.  The summand is a mu_6-CLASS function.
                                  On a SAMPLED set this only bites if two samples share a class --
                                  CHECKED (C-DUP), not assumed.
  (3) ** THE FIXED POINTS OF THE INVOLUTION ARE FORCED. **  S is symmetric under d <-> d^{-1}, and
      wherever d = +-d^{-1} (i.e. d^2 = +-1) the summand is r(d)^2 = +1 REGARDLESS OF THE DATA.
      Those terms are constants shared by data and null: zero information, pure dilution.
      COUNTED AND EXCLUDED (C-FIX), never averaged over.
  (4) the Gram/singular-value blindness theorem does NOT apply -- this is not a Gram spectrum.

NULL.  Permute b against a.  Preserves the marginals of a AND b EXACTLY (asserted, both sides) and
destroys only the pairing under inversion.  The null's own scale is checked against theory (sd = sqrt(M)).

CONTROLS -- every one measures BOTH sides of the comparison:
  C-BALANCE  the marginal of a and of b, reported separately, data and null.
  C-DUP      no two sampled d share a mu_6 class (which would force ties).
  C-FIX      count of d with d = +-d^{-1}; excluded from S.
  C-NULLSD   the null's empirical sd vs the theoretical sqrt(M_eff) -- catches a mis-scaled null
             (the fault that made every cell fire in item 4).
  C-PLANT    dilution curve: the detection floor is MEASURED, never assumed.
"""

import sys
import time
from random import Random
import numpy as np
from gmpy2 import powmod, invert, mpz

P = mpz(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F)
N = mpz(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141)
GX = mpz(0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798)
GY = mpz(0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
LAM = mpz(0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72)
HALF = (P - 1)//2


def jdbl(A):
    X, Y, Z = A
    if Y == 0:
        return (mpz(0), mpz(0), mpz(0))
    S = 4*X*Y*Y % P
    M_ = 3*X*X % P
    Xr = (M_*M_ - 2*S) % P
    return (Xr, (M_*(S - Xr) - 8*Y**4) % P, 2*Y*Z % P)


def jadd(A, B):
    X1, Y1, Z1 = A
    X2, Y2, Z2 = B
    if Z1 == 0:
        return B
    if Z2 == 0:
        return A
    Z1Z1 = Z1*Z1 % P
    Z2Z2 = Z2*Z2 % P
    U1 = X1*Z2Z2 % P
    U2 = X2*Z1Z1 % P
    S1 = Y1*Z2*Z2Z2 % P
    S2 = Y2*Z1*Z1Z1 % P
    if U1 == U2:
        return jdbl(A) if S1 == S2 else (mpz(0), mpz(0), mpz(0))
    H = (U2 - U1) % P
    R = (S2 - S1) % P
    H2 = H*H % P
    H3 = H2*H % P
    U1H2 = U1*H2 % P
    X3 = (R*R - H3 - 2*U1H2) % P
    return (X3, (R*(U1H2 - X3) - S1*H3) % P, Z1*Z2*H % P)


def jmul(k):
    R = (mpz(0), mpz(0), mpz(0))
    Q = (GX, GY, mpz(1))
    while k:
        if k & 1:
            R = jadd(R, Q)
        Q = jdbl(Q)
        k >>= 1
    return R


def batch_x(pts):
    zs = [p[2] for p in pts]
    pre = [mpz(1)]*(len(zs)+1)
    for i, z in enumerate(zs):
        pre[i+1] = pre[i]*z % P
    inv = invert(pre[-1], P)
    out = [None]*len(zs)
    for i in range(len(zs)-1, -1, -1):
        zi = inv*pre[i] % P
        inv = inv*zs[i] % P
        out[i] = pts[i][0]*zi % P*zi % P
    return out


def readout(ds):
    xs = batch_x([jmul(d % N) for d in ds])
    return np.array([1 if powmod(x, HALF, P) == 1 else -1 for x in xs], dtype=np.int64)


def perm_p(a, b, R, rng):
    S = int(np.dot(a, b))
    bb = b.copy()
    ge = 0
    Ss = []
    for _ in range(R):
        rng.shuffle(bb)
        v = int(np.dot(a, bb))
        Ss.append(v)
        if abs(v) >= abs(S):
            ge += 1
    return S, ge + 1, R + 1, float(np.std(Ss)), float(np.mean(Ss))


def arm(label, ds, R, rng, verbose=True):
    ds = [mpz(d) for d in ds]
    inv_ds = [invert(d, N) for d in ds]
    # C-FIX: fixed points of the involution contribute a forced +1
    fixed = [i for i, (d, e) in enumerate(zip(ds, inv_ds)) if e == d or e == (N - d) % N]
    keep = [i for i in range(len(ds)) if i not in set(fixed)]
    # C-DUP: any two samples in the same mu_6 class?
    seen = {}
    dup = 0
    for i in keep:
        d = ds[i]
        key = min(int(d), int(N-d), int(LAM*d % N), int(N-LAM*d % N),
                  int(LAM*LAM*d % N), int(N-LAM*LAM*d % N))
        if key in seen:
            dup += 1
        seen[key] = i
    a = readout([ds[i] for i in keep])
    b = readout([inv_ds[i] for i in keep])
    M = len(keep)
    S, num, den, sd, mu = perm_p(a, b, R, rng)
    if verbose:
        print("   %-22s M=%-6d C-FIX excl=%-3d C-DUP=%-3d | a: +%d/-%d  b: +%d/-%d"
              % (label, M, len(fixed), dup, int((a > 0).sum()), int((a < 0).sum()),
                 int((b > 0).sum()), int((b < 0).sum())), flush=True)
        print("        S=%-8d  null mean=%.2f sd=%.2f (theory sqrt(M)=%.2f, ratio %.3f)  perm p=%d/%d%s"
              % (S, mu, sd, M**0.5, sd/M**0.5, num, den, "  <-- FIRES" if num*20 <= den else ""),
              flush=True)
    return S, num, den, sd, M, a, b


if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    rng = Random(20260801)
    nprng = np.random.default_rng(20260801)
    t0 = time.time()
    print("="*100)
    print("ITEM 5 -- pointwise inversion  S = sum chi_2(x_[d]G) * chi_2(x_[d^-1]G)   M=%d  R=%d" % (M, R))
    print("="*100)
    print("  -- arms: d from the dyadic interval [2^(k-1), 2^k) --", flush=True)
    res = {}
    for k in (128, 135, 160):
        ds = [rng.randrange(2**(k-1), 2**k) for _ in range(M)]
        res[k] = arm("k=%d" % k, ds, R, np.random.default_rng(k))
    print("  -- control arm: d from the FULL range [1, n) --", flush=True)
    ds = [rng.randrange(1, int(N)) for _ in range(M)]
    res["full"] = arm("full-range", ds, R, np.random.default_rng(99))

    print("  -- C-PLANT dilution (floor MEASURED, on the k=128 arm) --", flush=True)
    _, _, _, _, Mk, a, b = res[128]
    thr = sorted(abs(int(np.dot(a, np.random.default_rng(s).permutation(b))))
                 for s in range(400))[396]
    for frac in (10, 5, 2, 1, 0.5, 0.2):
        bb = b.copy()
        m = int(Mk*frac/100)
        idx = nprng.choice(Mk, m, replace=False)
        bb[idx] = a[idx]                       # force agreement on a fraction
        v = abs(int(np.dot(a, bb)))
        print("     %5s%% planted: |S|=%-8d vs 99th=%-8d -> %s"
              % (frac, v, thr, "FIRES" if v >= thr else "-"), flush=True)
    print("  [%ds]" % (time.time()-t0))
