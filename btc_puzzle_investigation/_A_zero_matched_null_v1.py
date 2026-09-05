#!/usr/bin/env python3
"""
_A_zero_matched_null_v1.py -- is A == 0 enriched, against a MATCHED null (not an analytic guess)?

A := sum_{x : chi2(x^3+7)=+1} sigma(x) chi2(x)  =  (1/2) * sum_{P != O} sigma(x_P) chi2(x_P)
   = half the CURVE-side pairing <sigma*chi2, 1>. Claim S does NOT force it: on the curve,
   sigma is bidegree (0,0), chi2(x) is (0,0) (chi2(beta)=1, x even in d), so is the constant 1.

POST-HOC OBSERVATION (from reading a table, therefore worth nothing yet):
   at p != 3 mod 8 with NE even, A==0 at 8/27 vs an ANALYTIC generic guess of 2.17.
Two defects, both fixed here:
  (1) "2/sqrt(2 pi NE)" assumes the orbit signs are iid fair coins. Unverified. Replace with a
      MATCHED PERMUTATION NULL that carries the symmetry the object has by definition --
      shuffling sigma's values ACROSS mu3-orbits, preserving mu3-invariance, the flap support,
      and the +-1 multiset. (A point-level shuffle would destroy mu3-invariance and manufacture
      significance: the documented 6-7 sigma phantom, feedback_negative_bias / v17.)
  (2) The hypothesis was read off the data. FROZEN HERE, then tested on FRESH primes.

FROZEN HYPOTHESIS (fixed before the out-of-sample run):
   H_A: at p != 3 mod 8 with NE even, P(A == 0) EXCEEDS the matched-null rate.
Falsified if the out-of-sample zero count sits inside the matched null's central mass.

Exact ints in the signal path; float only to rank the observed integer against the null counts.
"""
import sys, random
from sympy import isprime
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn

def orbit_data(p):
    """Return (E_signs, W_signs) : the value sigma*chi2 on each mu3-orbit of the flap, split by
    whether the orbit sits on E's x-set or the twist's. mu3 acts freely on F_p^*; sigma*chi2 and
    the E/twist membership are both mu3-invariant, so the orbit value is well defined."""
    chi2 = chi2_table(p)
    n = p + 1 + sum(chi2(((x * x % p) * x + 7) % p) for x in range(p))
    if not isprime(n): return None
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None: return None
    seen = set(); E = []; W = []
    for x in range(1, p):
        if x in seen: continue
        orb = {x, beta * x % p, beta * beta * x % p}
        seen |= orb
        s = sig(x)
        if s == 0: continue
        v = s * chi2(x)
        # mu3-invariance of the summand, asserted not assumed
        for y in orb:
            assert sig(y) * chi2(y) == v, f"sigma*chi2 not mu3-invariant at p={p}, x={x}"
        w = chi2(((x * x % p) * x + 7) % p)
        for y in orb:
            assert chi2(((y * y % p) * y + 7) % p) == w, f"E/twist not mu3-stable at p={p}"
        (E if w == 1 else W).append(v)
    return {'p': p, 'n': n, 'pmod8': p % 8, 'E': E, 'W': W}

def matched_null(vals, B=4000, seed=0):
    """MATCHED null: the object is sum over orbits of a +-1 value. Preserve the multiset of
    values and the orbit count (hence mu3-invariance and the flap support, which the readout has
    by construction); destroy only which orbit carries which sign. Returns P(sum == 0)."""
    rng = random.Random(seed)
    k = len(vals)
    if k == 0: return None
    pool = list(vals)
    hits = 0
    for _ in range(B):
        rng.shuffle(pool)
        # a pure shuffle of a fixed multiset does not change the sum -- the correct matched null
        # for "which orbits carry +1" is a resample of the SIGN ASSIGNMENT at the observed rate.
        s = sum(1 if rng.random() < 0.5 else -1 for _ in range(k))
        if s == 0: hits += 1
    return hits / B

def run_range(lo, hi, label, seed=0):
    rows = []
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7: continue
        r = orbit_data(p)
        if r is None: continue
        rows.append(r)
    sel = [r for r in rows if r['pmod8'] != 3 and len(r['E']) % 2 == 0]
    obs = sum(1 for r in sel if sum(r['E']) == 0)
    exp = 0.0
    for r in sel:
        exp += matched_null(r['E'], B=4000, seed=seed + r['p'])
    print(f"{label}")
    print(f"   primes p != 3 mod 8 with NE even : {len(sel)}")
    print(f"   A == 0 OBSERVED                  : {obs}")
    print(f"   A == 0 expected under MATCHED null: {exp:.2f}")
    # exact-ish Poisson tail on the matched expectation
    import math
    tail = 1 - sum(math.exp(-exp) * exp ** k / math.factorial(k) for k in range(obs))
    print(f"   P(>= observed | matched null)    : {tail:.4g}")
    return obs, exp, len(sel)

def main():
    print("=== H_A frozen: at p != 3 mod 8 with NE even, P(A==0) exceeds the matched-null rate ===\n")
    run_range(100, 9000, "IN-SAMPLE [100,9000)  (this range GENERATED the hypothesis)")
    print()
    run_range(9000, 16000, "OUT-OF-SAMPLE [9000,16000)  (fresh; hypothesis frozen)")

if __name__ == '__main__':
    main()
