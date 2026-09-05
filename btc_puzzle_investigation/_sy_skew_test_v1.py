#!/usr/bin/env python3
"""
_sy_skew_test_v1.py -- executes PREREG_Sy_sign_skew_v1.md EXACTLY. No choices made post-hoc.

Sy_b(p) = sum over P!=O on y^2=x^3+b of s_y(P)*chi2(y_P), s_y=+1 iff y<=(p-1)/2. Canonical integer.
Sample: p in [10000,40000), p=1 mod6, p=3 mod4, n=#E(F_p) prime. (b=7 is the curve; C1 varies b.)
Exact ints; float only for the binomial p-value and the normalized mean (reporting).
"""
import sys, random, math
from sympy import isprime
from sympy.ntheory.residue_ntheory import sqrt_mod

def chi2_tab(p):
    qr = bytearray(p)
    for i in range(1, (p - 1) // 2 + 1): qr[i * i % p] = 1
    return lambda v: 0 if v % p == 0 else (1 if qr[v % p] else -1)

def order_curve(p, b, chi2):
    return p + 1 + sum(chi2((x * x % p) * x % p + b) for x in range(p))

def Sy(p, b, chi2, flip=False):
    """canonical: sum over all points, both (x,+-y). flip toggles the s_y convention."""
    half = (p - 1) // 2
    tot = 0
    for x in range(p):
        rhs = ((x * x % p) * x + b) % p
        c = chi2(rhs)
        if c != 1: continue
        y = sqrt_mod(rhs, p) % p
        for yy in (y, (p - y) % p):
            lower = yy <= half
            s = (1 if lower else -1)
            if flip: s = -s
            tot += s * chi2(yy)
    return tot

def main():
    lo, hi = 10000, 40000
    # fixed sample: p=1 mod6, p=3 mod4, n(#E for b=7) prime
    sample = []
    skipped = 0
    for p in range(lo, hi):
        if p % 6 != 1 or p % 4 != 3 or not isprime(p): continue
        chi2 = chi2_tab(p)
        if isprime(order_curve(p, 7, chi2)):
            sample.append(p)
        else:
            skipped += 1
    print(f"# sample: p in [{lo},{hi}), p=1 mod6 & 3 mod4, n(b=7) prime. M_candidates={len(sample)} "
          f"(skipped {skipped} for n composite)")

    # ---- PRIMARY S1 + S3 + convention flip, on b=7 ----
    vals = []
    for p in sample:
        chi2 = chi2_tab(p)
        vals.append((p, Sy(p, 7, chi2)))
    # S3: 6 | Sy  (must hold)
    div6 = all(v % 6 == 0 for _, v in vals)
    nz = [(p, v) for p, v in vals if v != 0]
    M = len(nz); k = sum(1 for _, v in nz if v > 0)
    # exact two-sided binomial p-value vs 1/2
    from math import comb
    def binom_two_sided(k, M):
        pmf = lambda i: comb(M, i) / 2 ** M
        obs = pmf(k)
        return sum(pmf(i) for i in range(M + 1) if pmf(i) <= obs * (1 + 1e-9))
    pval = binom_two_sided(k, M)
    s2 = sum(v / (2 * math.sqrt(p)) for p, v in nz) / M
    print(f"\n=== PRIMARY (b=7) ===")
    print(f"S3  6|Sy on all sample primes: {div6}   (must be True)")
    print(f"S1  sign lean: k/M = {k}/{M} = {k/M:.3f}   two-sided binom p = {pval:.4g}"
          f"   [CONFIRM iff p<0.01]")
    print(f"S2  mean Sy/(2 sqrt p) = {s2:+.3f}")

    # convention flip: skew must flip, magnitude identical
    kf = sum(1 for p in sample for v in [Sy(p, 7, chi2_tab(p), flip=True)] if v > 0)
    valsf = [(p, Sy(p, 7, chi2_tab(p), flip=True)) for p in sample]
    nzf = [(p, v) for p, v in valsf if v != 0]
    kf = sum(1 for _, v in nzf if v > 0)
    print(f"    convention-flip check: flipped k/M = {kf}/{len(nzf)}  (must be {len(nzf)-k}/{len(nzf)} "
          f"= mirror; else BUG)")

    # ---- C1 random-b control (the deck-check) ----
    print(f"\n=== C1 random-b control (is b=7 special or generic?) ===")
    for b in (1, 2, 3, 5, 11, 13, 17, 7):
        kk = 0; MM = 0
        for p in sample:
            chi2 = chi2_tab(p)
            v = Sy(p, b, chi2)
            if v != 0:
                MM += 1; kk += (v > 0)
        pv = binom_two_sided(kk, MM) if MM else 1.0
        tag = "  <-- the curve" if b == 7 else ""
        print(f"    b={b:>2}: k/M = {kk}/{MM} = {kk/MM:.3f}  binom p={pv:.4g}{tag}")

    # ---- C2 sign-shuffle null (calibration) ----
    rng = random.Random(20260718)
    ks = []
    for _ in range(1000):
        ks.append(sum(1 for _ in range(M) if rng.random() < 0.5))
    ks.sort()
    print(f"\n=== C2 shuffle null (M={M}) ===")
    print(f"    null k: mean {sum(ks)/len(ks):.1f}, central 90% = [{ks[50]},{ks[949]}]"
          f"   observed k={k}  ({'OUTSIDE null -> real' if k<ks[50] or k>ks[949] else 'inside null'})")

if __name__ == '__main__':
    main()
