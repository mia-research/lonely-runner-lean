#!/usr/bin/env python3
"""
Test Bertrand prime extension for Theorem 12.1 Case B.

Strategy: For |E_div|=2 with all dropped non-units, test if Bertrand prime witness
generalizes from representative tuple (speeds = residues) to actual speeds with
divisible runners having large q_0.

Key question: Can we find a Bertrand prime q and witness t=k/q such that:
1. All divisible runners q_0*n have ||q_0*n*k/q|| large (avoid loneliness)
2. All retained non-divisible runners have distance >= 1/n
3. Dropped non-units have distance < 1/n

Hypothesis: This is hard because divisible runners can satisfy ||q_0*n*k/q|| < 1/n
for certain (q, q_0) pairs by CRT.
"""

from math import gcd
from fractions import Fraction
import random

def frac_dist(num, denom):
    """Compute fractional distance ||num/denom|| = min(num mod denom, denom - num mod denom) / denom."""
    r = num % denom
    return min(r, denom - r) / denom

def test_bertrand_representative(n, d1, d2, q_prime):
    """
    Test if Bertrand prime q works for representative tuple (speeds = residues).

    Representative tuple: E_non = {1, 2, ..., n-1} \ {d1, d2},
                          E_div = {n, 2n} (two divisible runners)
    """
    # Find k such that d1 * k ≡ -1 (mod q)
    d1_inv = pow(d1, -1, q_prime)
    k = (-d1_inv) % q_prime

    if k == 0 or k >= q_prime:
        return None

    t = Fraction(k, q_prime)

    # Check d1: should be ~1/q
    dist_d1 = frac_dist(d1 * k, q_prime)
    if dist_d1 >= 1/n:
        return None  # d1 not close enough to 1/q

    # Check all retained residues
    for rho in range(1, n):
        if rho in {d1, d2}:
            continue
        dist_rho = frac_dist(rho * k, q_prime)
        if dist_rho < 1/n:
            return None  # Retained runner too close

    # Check divisible runners at speeds n and 2n (representative)
    for q_div in [1, 2]:
        e_div = q_div * n
        # distance = ||e_div * t|| = ||q_div * n * k / q||
        dist_div = frac_dist((q_div * n * k) % q_prime, q_prime)
        if dist_div < 1/n:
            return None  # Divisible runner too close

    return (t, dist_d1)

def test_bertrand_general_speeds(n, d1, d2, q_prime, q_divs):
    """
    Test if Bertrand prime q works with general divisible runner speeds q_divs.

    Problem: For fixed q, divisible runners with varying q_j can potentially satisfy
    ||q_j * n * k / q|| < 1/n via CRT, blocking the witness.
    """
    d1_inv = pow(d1, -1, q_prime)
    k = (-d1_inv) % q_prime

    if k == 0 or k >= q_prime:
        return None

    t = Fraction(k, q_prime)

    # Check d1
    dist_d1 = frac_dist(d1 * k, q_prime)
    if dist_d1 >= 1/n:
        return None

    # Check retained residues
    for rho in range(1, n):
        if rho in {d1, d2}:
            continue
        dist_rho = frac_dist(rho * k, q_prime)
        if dist_rho < 1/n:
            return None

    # Check divisible runners with actual q values
    for q_div in q_divs:
        e_div_residue = (q_div * n) % q_prime
        dist_div = frac_dist(e_div_residue * k, q_prime)
        if dist_div < 1/n:
            return False  # FAILS: divisible runner too close

    return (t, dist_d1)

def search_bertrand_extension(n, d1, d2, max_q=200):
    """
    Search for Bertrand primes that work for representative tuple.
    Then test a few adversarial divisible runner speed choices.
    """
    print(f"\n{'='*60}")
    print(f"Testing n={n}, dropped non-units ({d1}, {d2})")
    print(f"{'='*60}")

    primes = [p for p in range(n+1, min(2*n, max_q)) if all(p % d != 0 for d in range(2, int(p**0.5)+1) if d > 1)]

    rep_success = 0
    rep_witness = None

    for q in primes:
        result = test_bertrand_representative(n, d1, d2, q)
        if result:
            rep_success += 1
            if rep_witness is None:
                rep_witness = (q, result)

    print(f"Bertrand primes in ({n}, {2*n}): {len(primes)}")
    print(f"Successful for representative tuple: {rep_success}/{len(primes)}")

    if rep_witness:
        q, (t, dist_d1) = rep_witness
        print(f"  Example: q={q}, k={t.numerator}, dist(d1)={dist_d1:.4f}")

        # Now test with adversarial divisible runner speeds
        # Choose q_divs that might break the witness (via CRT)
        print(f"\nTesting extension to general speeds (divisible runners)...")

        test_cases = [
            (q, [1, 2]),  # Representative
            (q, [1, 3]),  # Different divisor
            (q, [2, 3]),  # Both not 1
            (q, [1, 79]),  # Large q_div (from counterexample)
        ]

        for q_test, q_divs in test_cases:
            result = test_bertrand_general_speeds(n, d1, d2, q_test, q_divs)
            status = "✓ PASS" if result else "✗ FAIL"
            print(f"  q={q_test}, q_divs={q_divs}: {status}")

    return rep_success > 0

if __name__ == "__main__":
    # Test cases from previous analysis
    search_bertrand_extension(n=15, d1=3, d2=6)
    search_bertrand_extension(n=15, d1=5, d2=10)
    search_bertrand_extension(n=21, d1=3, d2=6)
    search_bertrand_extension(n=21, d1=7, d2=14)
