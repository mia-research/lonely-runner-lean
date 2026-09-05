#!/usr/bin/env python3
"""
Coverage Profile Analysis: Find M-independent safe fibers.

For each fiber b in B_div, define:
  sigma(b) = (t_e(b))_{e in E_fixed}        -- M-independent signature
  C_fix(b) = Z_n \ union_bad_fixed(sigma(b))  -- elements NOT covered by fixed runners

If |C_fix(b)| >= 3: fiber is ALWAYS SAFE (M-runner can cover at most 2).
If |C_fix(b)| = 0: fiber is ALWAYS BAD (fixed runners already cover Z_n).
If |C_fix(b)| in {1,2}: fiber is conditionally bad (depends on inv(M) and t_M(b)).

KEY CLAIM: For any Case-2 family, at least n-1 fibers in B_div have |C_fix(b)| >= 3.
This would imply B_safe >= n-1 for ALL M (unconditionally).

We check this for n=5,7 and all-distinct E_fixed.
"""

from math import gcd
from itertools import combinations

def modinv(a, n):
    return pow(int(a), n - 2, n)

def lcm2(a, b):
    return a * b // gcd(a, b)

def lcm_list(lst):
    r = 1
    for x in lst:
        r = lcm2(r, x)
    return r

def bad_a_set(e, t, n):
    inv_e = modinv(e, n)
    a0 = (-t * inv_e) % n
    a1 = ((n - 1 - t) * inv_e) % n
    return frozenset({a0, a1})

def coverage_profile(E_fixed, n, M, L0):
    """
    For each fiber b in B_div, compute |C_fix(b)| where C_fix(b) = Z_n minus
    the union of bad_a from FIXED runners only (M-independent part).

    Returns histogram: {0: count, 1: count, 2: count, >=3: count}
    Also returns: count of fibers with |C_fix| >= 3 (always-safe count).
    """
    L = L0 * M
    b_lo = L // n
    b_hi = (n - 1) * L // n

    hist = {0: 0, 1: 0, 2: 0, 3: 0}
    always_safe_count = 0

    for b in range(b_lo, b_hi + 1):
        # Fixed-runner union_bad (M-independent by PL.1 logic for fixed runners)
        union_fixed = set()
        for e in E_fixed:
            union_fixed |= bad_a_set(e, (e * b) // L, n)

        c_fix = n - len(union_fixed)  # |Z_n \ union_fixed|

        if c_fix >= 3:
            hist[3] += 1
            always_safe_count += 1
        else:
            hist[min(c_fix, 3)] += 1

    return hist, always_safe_count


def M_independent_always_safe(E_fixed, n, L0, max_M=5):
    """
    Compute the count of fibers with |C_fix(b)| >= 3 (always-safe regardless of M).

    Note: sigma(b) depends on M via L=L0*M (the floor quotients change with M).
    So we compute this for several M values.
    """
    results = {}
    for M in range(1, max_M + 1):
        if gcd(M, L0) != 1 or M % n == 0:
            continue
        hist, always_safe = coverage_profile(E_fixed, n, M, L0)
        B_div = (n - 2) * L0 * M // n + 1  # approximate
        results[M] = (hist, always_safe)
    return results


def analyze_fixed_signature_structure(E_fixed, n, M, L0):
    """
    Deeper analysis: for the worst-case M, show which fibers are always-safe
    (|C_fix| >= 3) and which depend on M's coverage.
    """
    L = L0 * M
    b_lo = L // n
    b_hi = (n - 1) * L // n

    always_safe = []   # |C_fix| >= 3
    sometimes_bad_1 = []  # |C_fix| = 1
    sometimes_bad_2 = []  # |C_fix| = 2
    always_bad = []    # |C_fix| = 0

    for b in range(b_lo, b_hi + 1):
        union_fixed = set()
        for e in E_fixed:
            union_fixed |= bad_a_set(e, (e * b) // L, n)
        c_fix = set(range(n)) - union_fixed
        sz = len(c_fix)

        if sz >= 3:
            always_safe.append(b)
        elif sz == 2:
            sometimes_bad_2.append((b, frozenset(c_fix)))
        elif sz == 1:
            sometimes_bad_1.append((b, frozenset(c_fix)))
        else:
            always_bad.append(b)

    return always_safe, sometimes_bad_1, sometimes_bad_2, always_bad


def run_coverage_analysis(n, max_M=50):
    print(f"\n{'='*60}")
    print(f"n = {n}, phi(n) = {n-1}")
    print(f"KEY CLAIM: for all E_fixed (all-distinct), at least {n-1} fibers have |C_fix|>=3")

    # Find worst case: family + M with fewest always-safe fibers
    global_min_always_safe = None
    global_worst = None

    for E_fixed in combinations(range(1, n), n - 3):
        if gcd(*E_fixed) != 1:
            continue
        L0 = lcm_list(list(E_fixed) + [n])

        # Check bottom missing is 2 (truly all-distinct)
        bu = {0} | {((n - 1) * modinv(e, n)) % n for e in E_fixed}
        bm = set(range(n)) - bu
        if len(bm) != 2:
            continue

        for M in range(1, max_M + 1):
            if gcd(M, L0) != 1 or M % n == 0:
                continue

            hist, always_safe_ct = coverage_profile(E_fixed, n, M, L0)
            L = L0 * M
            B_div = (n - 1) * L // n - L // n + 1

            if global_min_always_safe is None or always_safe_ct < global_min_always_safe:
                global_min_always_safe = always_safe_ct
                global_worst = (E_fixed, M, L0, B_div, hist, always_safe_ct)

    if global_worst:
        E_fixed, M, L0, B_div, hist, as_ct = global_worst
        print(f"\n  Worst case: E_fixed={E_fixed}, M={M}, L0={L0}")
        print(f"  B_div={B_div}")
        print(f"  Coverage histogram:")
        print(f"    |C_fix|=0 (always bad): {hist[0]}")
        print(f"    |C_fix|=1 (cond. bad):  {hist[1]}")
        print(f"    |C_fix|=2 (cond. bad):  {hist[2]}")
        print(f"    |C_fix|>=3 (ALWAYS SAFE): {hist[3]}  [need >= {n-1}]")
        print(f"  CLAIM HOLDS: {hist[3] >= n-1}")

        # Show structure of always-safe fibers
        always_safe, sb1, sb2, always_bad = analyze_fixed_signature_structure(
            list(E_fixed), n, M, L0)
        print(f"\n  Always-safe fibers (first 5): {always_safe[:5]} ...")
        print(f"  Always-bad fibers (first 5): {always_bad[:5]} ...")

        # Check: do the always-safe fibers persist as M increases?
        print(f"\n  Always-safe count vs M (for this E_fixed={E_fixed}):")
        for M2 in range(1, 30):
            if gcd(M2, L0) != 1 or M2 % n == 0:
                continue
            _, as2 = coverage_profile(E_fixed, n, M2, L0)
            B_div2 = (n - 1) * L0 * M2 // n - L0 * M2 // n + 1
            print(f"    M={M2:3d}: always_safe={as2:5d}  B_div={B_div2:5d}  ratio={as2/B_div2:.3f}")
            if M2 >= 20:
                break


def check_always_safe_lower_bound(n, max_M=200):
    """
    Check: for all E_fixed (all-distinct) and all M up to max_M,
    is count(|C_fix(b)| >= 3) >= n-1?
    If yes: B_safe >= n-1 for ALL M (M-independent lower bound).
    """
    print(f"\n{'='*60}")
    print(f"n={n}: Checking always-safe count >= {n-1} for all families, M <= {max_M}")

    violations = []
    min_always_safe_seen = None
    min_info = None

    for E_fixed in combinations(range(1, n), n - 3):
        if gcd(*E_fixed) != 1:
            continue
        L0 = lcm_list(list(E_fixed) + [n])

        bu = {0} | {((n - 1) * modinv(e, n)) % n for e in E_fixed}
        bm = set(range(n)) - bu
        if len(bm) != 2:
            continue

        for M in range(1, max_M + 1):
            if gcd(M, L0) != 1 or M % n == 0:
                continue

            _, as_ct = coverage_profile(E_fixed, n, M, L0)
            if min_always_safe_seen is None or as_ct < min_always_safe_seen:
                min_always_safe_seen = as_ct
                min_info = (E_fixed, M, L0, as_ct)

            if as_ct < n - 1:
                violations.append((E_fixed, M, as_ct))

    print(f"  Total violations (always_safe < n-1): {len(violations)}")
    print(f"  Min always-safe seen: {min_always_safe_seen} at {min_info}")
    return violations


if __name__ == '__main__':
    # Main analysis
    for n in [5, 7]:
        run_coverage_analysis(n, max_M=30)

    # Rigorous check
    print("\n" + "="*60)
    print("RIGOROUS CHECK: always-safe count >= n-1 for all families")
    check_always_safe_lower_bound(5, max_M=500)
    check_always_safe_lower_bound(7, max_M=100)
