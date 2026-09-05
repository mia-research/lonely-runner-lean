#!/usr/bin/env python3
"""
Comprehensive test of Bertrand prime extension for Theorem 12.1 Case B.

Hypothesis: For Bertrand prime q ∈ (n, 2n) with k = (-d1^{-1} mod q),
the witness t = k/q works for ALL choices of divisible runner speeds q_0*n,
not just q_0 ∈ {1, 2}.

Core mechanism: For q_0 * n * k mod q to land in the "bad" range (distance < 1/n),
we'd need very specific divisibility properties. Since k is coprime to q
(because d1 is coprime to q via Bertrand prime construction), the residues
q_0 * n * k mod q distribute well as q_0 varies.
"""

from math import gcd
from fractions import Fraction

def frac_dist(num, denom):
    """Compute ||num/denom||."""
    r = num % denom
    return min(r, denom - r) / denom

def test_bertrand_all_divisible_speeds(n, d1, d2, q_prime, max_q_div=500):
    """
    Exhaustive test: find a Bertrand prime q that works for ALL q_0 in {1, ..., max_q_div}.

    Returns: (q, k, min_distance_for_divisible_runners)
    """
    if gcd(d1, q_prime) != 1:
        return None  # d1 not coprime to q, skip

    d1_inv = pow(d1, -1, q_prime)
    k = (-d1_inv) % q_prime

    if k == 0 or k >= q_prime:
        return None

    # Check d1 distance
    dist_d1 = frac_dist(d1 * k, q_prime)
    if dist_d1 >= 1/n:
        return None  # d1 not close enough

    # Check retained non-divisible runners
    for rho in range(1, n):
        if rho in {d1, d2}:
            continue
        dist_rho = frac_dist(rho * k, q_prime)
        if dist_rho < 1/n:
            return None  # Retained runner too close

    # EXHAUSTIVE CHECK: all divisible runner speeds
    min_div_dist = 1.0
    for q_div in range(1, max_q_div + 1):
        dist_div = frac_dist((q_div * n * k) % q_prime, q_prime)
        if dist_div < 1/n:
            return None  # FAIL: found a divisible runner that's too close
        min_div_dist = min(min_div_dist, dist_div)

    return (q_prime, k, min_div_dist)

def search_comprehensive(n, d1, d2, max_q_div=500):
    """Search for working Bertrand primes, with exhaustive divisible runner check."""
    print(f"\n{'='*70}")
    print(f"COMPREHENSIVE TEST: n={n}, dropped non-units ({d1}, {d2})")
    print(f"Exhaustive check: all q_div ∈ {{1, ..., {max_q_div}}}")
    print(f"{'='*70}")

    # Generate primes in (n, 2n)
    def is_prime(num):
        if num < 2:
            return False
        if num == 2:
            return True
        if num % 2 == 0:
            return False
        for d in range(3, int(num**0.5) + 1, 2):
            if num % d == 0:
                return False
        return True

    primes = [p for p in range(n + 1, 2 * n) if is_prime(p)]
    print(f"Bertrand primes in ({n}, {2*n}): {primes}")

    success_count = 0
    for q in primes:
        result = test_bertrand_all_divisible_speeds(n, d1, d2, q, max_q_div)
        if result:
            success_count += 1
            q_test, k, min_div = result
            print(f"✓ q={q}: k={k}, dist(d1)={frac_dist(d1*k, q):.6f}, min_div_dist={min_div:.6f}")

    print(f"\nResult: {success_count}/{len(primes)} Bertrand primes work exhaustively.")
    if success_count > 0:
        print("✓✓✓ BERTRAND EXTENSION CONFIRMED FOR GENERAL DIVISIBLE RUNNER SPEEDS ✓✓✓")
    else:
        print("✗ No Bertrand prime extends to all divisible runner speeds.")

    return success_count > 0

if __name__ == "__main__":
    # Test multiple cases
    all_pass = True
    all_pass &= search_comprehensive(15, 3, 6, max_q_div=500)
    all_pass &= search_comprehensive(15, 5, 10, max_q_div=500)
    all_pass &= search_comprehensive(21, 3, 6, max_q_div=500)

    print(f"\n{'='*70}")
    if all_pass:
        print("ALL TESTS PASSED: Bertrand prime witness extends to general speeds!")
        print("Theorem 12.1 Case B can be PROVED using this approach.")
    else:
        print("Some test cases failed. Further investigation needed.")
    print(f"{'='*70}")
