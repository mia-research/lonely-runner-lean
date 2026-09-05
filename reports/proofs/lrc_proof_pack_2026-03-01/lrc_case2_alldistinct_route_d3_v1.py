#!/usr/bin/env python3
"""
Route D.3 Analysis: All-Distinct Fixed Speeds Case
===================================================
For Case-2 LRC with |E_fixed| = n-3 distinct speeds (each appearing exactly once),
the quasi-lower-band argument gives only 2 missing elements (not 3), so the
F1246689 proof doesn't directly apply.

This script:
1. Enumerates all all-distinct Case-2 families for n=5,7
2. Computes exact B_safe for all valid M up to max_M
3. Identifies the mechanism of safety in worst cases
4. Checks: for each "bad M" (one that allows coverage in quasi-lower band),
   does the complement region still give enough safe fibers?
"""

from math import gcd
from itertools import combinations

# ── helpers ──────────────────────────────────────────────────────────────────

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

def compute_coverage(E_fixed, n, M, L0):
    """
    Compute exact (B_div_count, C_bad, B_safe).
    E = E_fixed ∪ {M, n}.  L = L0*M.
    B_div = {b in [L0*M/n, (n-1)*L0*M/n]}.
    """
    L = L0 * M
    b_lo = L // n            # = L0*M/n (exact, since n | L0)
    b_hi = (n - 1) * L // n  # = (n-1)*L0*M/n
    B_div_count = b_hi - b_lo + 1

    C_bad = 0
    for b in range(b_lo, b_hi + 1):
        union_bad = set()
        for e in E_fixed:
            union_bad |= bad_a_set(e, (e * b) // L, n)
        t_M = b // L0   # PL.1: floor(M*b/(L0*M)) = floor(b/L0), M-independent
        union_bad |= bad_a_set(M, t_M, n)
        if len(union_bad) == n:
            C_bad += 1

    return B_div_count, C_bad, B_div_count - C_bad


def bottom_missing(E_fixed, n):
    """Missing elements from Z_n in the bottom band (t_e=0 all e)."""
    union = {0}
    for e in E_fixed:
        union.add(((n - 1) * modinv(e, n)) % n)
    return frozenset(set(range(n)) - union)


def top_missing(E_fixed, n):
    """Missing elements from Z_n in the top band (t_e=e-1 all e)."""
    # bad_a(e, e-1, n) = {(-(e-1))*inv(e), (n-e)*inv(e)} mod n
    union = set()
    for e in E_fixed:
        inv_e = modinv(e, n)
        a0 = (-(e - 1) * inv_e) % n
        a1 = ((n - e) * inv_e) % n
        union.add(a0)
        union.add(a1)
    return frozenset(set(range(n)) - union)


# ── main analysis ─────────────────────────────────────────────────────────────

def analyze_bad_M_mechanism(E_fixed, n, M, L0, bm_set):
    """
    For a 'bad M' (one where quasi-lower band has some bad fibers),
    classify each fiber in B_div:
      - quasi_lower: b in [L0*M/n, L0*M/max(E_fixed))
      - quasi_upper: b in ((n-1)*L0*M/max(E_fixed), (n-1)*L0*M/n]
      - middle: everything else
    Count safe fibers in each region.
    """
    L = L0 * M
    b_lo = L // n
    b_hi = (n - 1) * L // n
    max_e = max(E_fixed)

    ql_hi = (L // max_e) - 1   # quasi-lower: b < L/max_e
    qu_lo = ((n - 1) * L + max_e - 1) // max_e  # quasi-upper: b > (n-1)L/max_e

    region_safe = {'quasi_lower': 0, 'quasi_upper': 0, 'middle': 0}
    region_total = {'quasi_lower': 0, 'quasi_upper': 0, 'middle': 0}

    for b in range(b_lo, b_hi + 1):
        if b <= ql_hi:
            region = 'quasi_lower'
        elif b >= qu_lo:
            region = 'quasi_upper'
        else:
            region = 'middle'
        region_total[region] += 1

        union_bad = set()
        for e in E_fixed:
            union_bad |= bad_a_set(e, (e * b) // L, n)
        t_M = b // L0
        union_bad |= bad_a_set(M, t_M, n)
        if len(union_bad) < n:
            region_safe[region] += 1

    return region_safe, region_total


def run_analysis(n, max_M=300):
    print(f"\n{'='*60}")
    print(f"n = {n}, phi(n) = {n-1}, need B_safe >= {n-1} for all M")
    print(f"All-distinct case: |E_fixed| = {n-3} speeds (each once)")

    violations = []
    family_results = []

    for E_fixed in combinations(range(1, n), n - 3):
        if gcd(*E_fixed) != 1:
            continue
        L0 = lcm_list(list(E_fixed) + [n])

        bm = bottom_missing(E_fixed, n)
        tm = top_missing(E_fixed, n)
        if len(bm) != 2:
            continue  # repeated inv(e): not truly all-distinct in coverage

        # Compute bad-M values for bottom band
        m1, m2 = sorted(bm)
        diff = (m2 - m1) % n
        # (n-1)*inv(M) ≡ ±diff (mod n) => inv(M) ≡ ±diff*(n-1)^{-1} ≡ ±diff*(-1) ≡ ∓diff (mod n)
        bad_invM_vals = {(-diff) % n, diff % n}  # = {n-diff, diff}

        worst_Bsafe = None
        worst_M_info = None

        for M in range(1, max_M + 1):
            if gcd(M, L0) != 1 or M % n == 0:
                continue

            Bdiv, Cbad, Bsafe = compute_coverage(list(E_fixed), n, M, L0)
            inv_M_mod_n = modinv(M, n)
            is_bad_M = inv_M_mod_n in bad_invM_vals

            if worst_Bsafe is None or Bsafe < worst_Bsafe:
                worst_Bsafe = Bsafe
                worst_M_info = (M, Bdiv, Cbad, Bsafe, is_bad_M, inv_M_mod_n)

            if Bsafe < n - 1:
                violations.append((n, E_fixed, M, Bdiv, Cbad, Bsafe))

        if worst_M_info is not None:
            M, Bd, Cb, Bs, is_bad, invM = worst_M_info
            vflag = " *** VIOLATION ***" if Bs < n - 1 else ""
            print(f"\n  E_fixed={E_fixed}  L0={L0}  bottom_miss={bm}  top_miss={tm}")
            print(f"    bad_invM = {bad_invM_vals}")
            print(f"    worst: M={M} (inv(M)={invM}, bad_M={is_bad}) "
                  f"B_div={Bd} C_bad={Cb} B_safe={Bs}{vflag}")

            # For worst M: show region breakdown
            reg_safe, reg_total = analyze_bad_M_mechanism(
                list(E_fixed), n, M, L0, bm)
            print(f"    region breakdown (safe/total): "
                  f"QL={reg_safe['quasi_lower']}/{reg_total['quasi_lower']}  "
                  f"MID={reg_safe['middle']}/{reg_total['middle']}  "
                  f"QU={reg_safe['quasi_upper']}/{reg_total['quasi_upper']}")

            family_results.append({
                'E_fixed': E_fixed, 'L0': L0, 'bm': bm, 'tm': tm,
                'bad_invM': bad_invM_vals, 'worst_Bsafe': Bs, 'worst_M': M
            })

    print(f"\n  Total violations (B_safe < n-1): {len(violations)}")
    return family_results, violations


# ── also: for each n, check the "critical j" argument ─────────────────────────

def critical_j_analysis(E_fixed, n, M, L0):
    """
    For given M, identify which j = t_M(b) values in the quasi-lower band
    can potentially lead to full coverage, and how many bad fibers result.
    """
    L = L0 * M
    b_lo = L // n
    max_e = max(E_fixed)
    ql_cutoff = L // max_e  # quasi-lower: b < ql_cutoff

    # Bottom missing
    bm = bottom_missing(E_fixed, n)
    m1, m2 = sorted(bm)

    # For t_M = j: bad_a(M,b) = {(-j)*inv(M), (n-1-j)*inv(M)} mod n
    inv_M = modinv(M, n)
    # This equals {m1,m2} iff the set matches. Check for each j:
    bad_j_vals = []
    for j in range(0, (ql_cutoff // L0) + 2):
        a0 = (-j * inv_M) % n
        a1 = ((n - 1 - j) * inv_M) % n
        if frozenset({a0, a1}) == frozenset(bm):
            bad_j_vals.append(j)

    return bad_j_vals


# ── run ───────────────────────────────────────────────────────────────────────

if __name__ == '__main__':
    results5, viol5 = run_analysis(n=5, max_M=400)
    results7, viol7 = run_analysis(n=7, max_M=300)

    print("\n" + "="*60)
    print("SUMMARY")
    print(f"n=5 violations: {len(viol5)}")
    print(f"n=7 violations: {len(viol7)}")

    # Show worst case across all families for n=7
    if results7:
        worst = min(results7, key=lambda x: x['worst_Bsafe'])
        print(f"\nWorst n=7 family: E_fixed={worst['E_fixed']} "
              f"B_safe_min={worst['worst_Bsafe']} at M={worst['worst_M']}")

    # Critical-j analysis for a specific bad case
    n = 7
    E_fixed = (1, 2, 3, 6)  # The all-distinct case computed earlier
    L0 = lcm_list(list(E_fixed) + [n])
    # Find a bad M:
    bm = bottom_missing(E_fixed, n)
    m1, m2 = sorted(bm)
    diff = (m2 - m1) % n
    bad_invM_vals = {(-diff) % n, diff % n}

    print(f"\n--- Critical-j analysis for n={n}, E_fixed={E_fixed}, bm={bm} ---")
    for M in range(1, 50):
        if gcd(M, L0) != 1 or M % n == 0:
            continue
        inv_M = modinv(M, n)
        if inv_M in bad_invM_vals:
            bad_j = critical_j_analysis(list(E_fixed), n, M, L0)
            L = L0 * M
            ql_cutoff = L // max(E_fixed)
            ql_start = L // n
            n_blocks = (ql_cutoff - ql_start) // L0
            _, Cbad, Bsafe = compute_coverage(list(E_fixed), n, M, L0)
            print(f"  M={M} inv(M)={inv_M} bad_j_vals={bad_j} "
                  f"QL_blocks≈{n_blocks} C_bad={Cbad} B_safe={Bsafe}")
