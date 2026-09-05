"""
B_safe Verification Script

Tests whether B_safe >= phi(n)(n-2)/2 holds for U-FORCE configurations.

U-FORCE: both dropped runners are non-units of Z_n, so all phi(n) units remain
in E_fix. We compute B_safe = x_0(E_fix) for E_fix = (all units of Z_n) union {n}.

The claim (Theorem 8.3) is: B_safe >= phi(n)(n-2)/2.

NOTE: E_fix has phi(n)+1 elements. In the actual LRC problem, |E_fix| = n-3.
For n=6: phi(6)+1 = 3 = n-3 = 3 (matches).
For n=8: phi(8)+1 = 5 = n-3 = 5 (matches).
For n=9: phi(9)+1 = 7 > n-3 = 6 (overconstrained -- our B_safe is a LOWER BOUND).
For n=10: phi(10)+1 = 5 = n-3 = 7? No, n-3=7 > 5 (underconstrained? Need more runners).

We also test with E_fix = (all units) ∪ {n} ∪ {extra non-unit runners} to match |E_fix| = n-3.
"""

from math import gcd
from functools import reduce
import itertools


def lcm(a, b):
    return a * b // gcd(a, b)


def lcm_list(lst):
    return reduce(lcm, lst, 1)


def euler_phi(n):
    result = n
    temp = n
    p = 2
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            result -= result // p
        p += 1
    if temp > 1:
        result -= result // temp
    return result


def units_of(n):
    return [e for e in range(1, n) if gcd(e, n) == 1]


def non_units_of(n):
    return [e for e in range(1, n) if gcd(e, n) > 1]


def compute_x0(E, n):
    """
    Compute x_0(E) = #{k in {1,...,N-1} : e*k mod N in [L, (n-1)*L] for all e in E}.
    Returns (x_0, L, N).
    """
    E = list(E)
    L = lcm_list(E)
    N = n * L
    lo = L
    hi = (n - 1) * L
    count = 0
    for k in range(1, N):
        if all(lo <= (e * k) % N <= hi for e in E):
            count += 1
    return count, L, N


def test_n(n):
    """
    Test B_safe >= phi(n)(n-2)/2 for n.
    Tests multiple U-FORCE configurations.
    """
    phi_n = euler_phi(n)
    bound = phi_n * (n - 2) / 2
    U = units_of(n)        # all units of Z_n
    NU = non_units_of(n)   # non-units of Z_n (elements of {1,...,n-1} with gcd > 1)
    # Multiples of n (divisible runners)
    multiples_of_n = [n]   # simplest: just n itself

    print(f"\n{'='*60}")
    print(f"n = {n}")
    print(f"phi(n) = {phi_n}")
    print(f"phi(n)(n-2)/2 = {bound}")
    print(f"Units of Z_{n}: {U}")
    print(f"Non-units in {{1,...,n-1}}: {NU}")
    print(f"Target |E_fix| = n-3 = {n-3}")
    print(f"|U| = phi(n) = {phi_n}")

    results = []

    # Config 1: E_fix = all units + divisible runner n
    # (may be over- or under-constrained relative to n-3)
    E_fix_basic = sorted(U + [n])
    x0, L, N = compute_x0(E_fix_basic, n)
    target_size = n - 3
    print(f"\n  Config 1: E_fix = units ∪ {{n}} = {E_fix_basic}")
    print(f"  |E_fix| = {len(E_fix_basic)} (target: {target_size})")
    print(f"  L = {L}, N = {N}")
    print(f"  B_safe = x_0(E_fix) = {x0}")
    print(f"  phi(n)(n-2)/2 = {bound}")
    print(f"  B_safe >= phi(n)(n-2)/2? {'YES' if x0 >= bound else 'NO *** VIOLATION ***'}")
    print(f"  B_safe >= phi(n)? {'YES' if x0 >= phi_n else 'NO *** VIOLATION ***'}")
    results.append(('basic', x0, bound, phi_n))

    # Config 2: E_fix with exactly n-3 elements (add non-units to reach target size)
    # We want E_fix to contain all phi(n) units + divisible runner + extra non-units
    needed_extra = target_size - len(E_fix_basic)
    if needed_extra > 0 and len(NU) >= needed_extra:
        # Try all combinations of extra non-units
        min_x0 = None
        min_config = None
        for extras in itertools.combinations(NU, needed_extra):
            E_fix_full = sorted(U + [n] + list(extras))
            x0_full, L_full, N_full = compute_x0(E_fix_full, n)
            if min_x0 is None or x0_full < min_x0:
                min_x0 = x0_full
                min_config = E_fix_full
        print(f"\n  Config 2 (worst case, |E_fix|=n-3): E_fix = {min_config}")
        print(f"  B_safe = {min_x0}")
        print(f"  B_safe >= phi(n)(n-2)/2? {'YES' if min_x0 >= bound else 'NO *** VIOLATION ***'}")
        print(f"  B_safe >= phi(n)? {'YES' if min_x0 >= phi_n else 'NO *** VIOLATION ***'}")
        results.append(('full', min_x0, bound, phi_n))
    elif needed_extra < 0:
        # We have too many elements in basic config; remove some units? No, that breaks U-FORCE.
        # Instead, use only units + one divisible runner (as above, already done).
        print(f"\n  Config 2: skipped (phi(n)+1 = {phi_n+1} > n-3 = {target_size}, basic config is overconstrained)")

    # Config 3: Vary the divisible runner (2n, 3n, ...)
    for k in range(2, min(4, n)):
        e_div = k * n
        E_fix_alt = sorted(U + [e_div])
        x0_alt, L_alt, N_alt = compute_x0(E_fix_alt, n)
        print(f"\n  Config 3 (e_div={e_div}): E_fix = {E_fix_alt}, B_safe = {x0_alt}")
        print(f"  B_safe >= phi(n)(n-2)/2? {'YES' if x0_alt >= bound else 'NO *** VIOLATION ***'}")
        results.append((f'e_div={e_div}', x0_alt, bound, phi_n))

    # Summary for this n
    all_pass_bound = all(r[1] >= r[2] for r in results)
    all_pass_phi = all(r[1] >= r[3] for r in results)
    min_observed = min(r[1] for r in results)
    print(f"\n  SUMMARY for n={n}:")
    print(f"  Min observed B_safe = {min_observed}")
    print(f"  phi(n)(n-2)/2 = {bound}")
    print(f"  phi(n) = {phi_n}")
    print(f"  All configs satisfy B_safe >= phi(n)(n-2)/2? {all_pass_bound}")
    print(f"  All configs satisfy B_safe >= phi(n)? {all_pass_phi}")

    return results


def main():
    print("B_safe Verification for Theorem 8.3 (Z0S.3)")
    print("Claim: Under U-FORCE, B_safe >= phi(n)(n-2)/2")
    print()

    # Test small composite n
    test_ns = [4, 6, 8, 9, 10, 12]

    all_results = {}
    for n in test_ns:
        try:
            results = test_n(n)
            all_results[n] = results
        except Exception as e:
            print(f"  ERROR for n={n}: {e}")

    # Final summary table
    print(f"\n{'='*60}")
    print("FINAL SUMMARY")
    print(f"{'='*60}")
    print(f"{'n':>4} | {'phi(n)':>6} | {'phi(n)(n-2)/2':>14} | {'min B_safe':>10} | {'>= bound?':>10} | {'>= phi(n)?':>10}")
    print('-' * 65)
    for n, results in all_results.items():
        phi_n = euler_phi(n)
        bound = phi_n * (n - 2) / 2
        min_bs = min(r[1] for r in results)
        ok_bound = min_bs >= bound
        ok_phi = min_bs >= phi_n
        print(f"{n:>4} | {phi_n:>6} | {bound:>14.1f} | {min_bs:>10} | {str(ok_bound):>10} | {str(ok_phi):>10}")

    print()
    violations = [(n, r) for n, results in all_results.items() for r in results if r[1] < r[2]]
    if violations:
        print(f"*** THEOREM 8.3 HAS {len(violations)} VIOLATION(S) — BOUND IS FALSE ***")
        for n, r in violations:
            print(f"  n={n}, config={r[0]}: B_safe={r[1]} < phi(n)(n-2)/2={r[2]}")
    else:
        print("All tested configs satisfy B_safe >= phi(n)(n-2)/2. Statement appears TRUE.")
        print("NOTE: Need new proof (current proof argument is invalid).")


if __name__ == '__main__':
    main()
