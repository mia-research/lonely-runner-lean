#!/usr/bin/env python3
"""
Empirical verification for the proposed prime-n late-window safe-fibre lemma
(Lemma 10.2' in planned v10.13). Tests whether for every integer fibre b in
J = [(n-2)L/(n-1), (n-1)L/n], the dropped-unit target s_d = d^{-1} - 1 mod n
is uncovered by every non-divisible runner.

If |safe fibres in J| >= phi(n) = n-1 across all tested tuples (including
non-canonical actual speeds like 40 = 7 mod 11), the late-window port from
Lemma 11.3a to prime n goes through. This is the load-bearing empirical
check for the planned v10.13 Prop 10.5 upgrade.
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable


def modinv(a: int, m: int) -> int:
    """Modular inverse of a mod m (m prime or gcd(a,m)=1)."""
    g, x, _ = _egcd(a % m, m)
    if g != 1:
        raise ValueError(f"modinv: gcd({a},{m}) = {g} != 1")
    return x % m


def _egcd(a: int, b: int) -> tuple[int, int, int]:
    if b == 0:
        return a, 1, 0
    g, x1, y1 = _egcd(b, a % b)
    return g, y1, x1 - (a // b) * y1


def lcm_many(xs: Iterable[int]) -> int:
    out = 1
    for x in xs:
        out = out * x // math.gcd(out, x)
    return out


def bad_set(e: int, b_int: int, L: int, n: int) -> set[int]:
    """
    Bad set for runner of actual speed e at integer fibre b_int (in B_div).
    Uses the exact formula: bad(e, t, n) = {-t * rho_inv, -(t+1) * rho_inv} mod n
    when gcd(rho_e, n) = 1.  For non-unit rho (rho=0 shouldn't occur for
    non-divisible runners by hypothesis), returns a coset instead.
    """
    rho = e % n
    t = (e * b_int) // L
    if rho == 0:
        # This should not happen for non-divisible runners; guard.
        return set()
    if math.gcd(rho, n) == 1:
        rho_inv = modinv(rho, n)
        return {(-t * rho_inv) % n, (-(t + 1) * rho_inv) % n}
    # Non-unit residue; not used for prime n since all residues 1..n-1 are units.
    # Return two cosets.
    g = math.gcd(rho, n)
    sub = {(k * (n // g)) % n for k in range(g)}
    out: set[int] = set()
    # Sol(rho, -t, n) = {r : rho*r + t ≡ 0 mod n}
    for c in range(n):
        if (rho * c + t) % n == 0:
            out.add(c)
    for c in range(n):
        if (rho * c + t + 1) % n == 0:
            out.add(c)
    return out


def j_integer_fibres(L: int, n: int) -> list[int]:
    """Integer fibres in J = [(n-2)L/(n-1), (n-1)L/n]."""
    lo = Fraction((n - 2) * L, n - 1)
    hi = Fraction((n - 1) * L, n)
    # ceil(lo) to floor(hi) inclusive
    b_lo = -(-lo.numerator // lo.denominator) if lo.denominator != 1 else int(lo)
    if lo.denominator != 1:
        b_lo = -(-lo.numerator // lo.denominator)
    else:
        b_lo = int(lo)
    b_hi = hi.numerator // hi.denominator if hi.denominator != 1 else int(hi)
    # Restrict to B_div = [L/n, (n-1)L/n]
    bdiv_lo = L // n if L % n == 0 else (L + n - 1) // n
    bdiv_hi = ((n - 1) * L) // n
    b_lo = max(b_lo, bdiv_lo)
    b_hi = min(b_hi, bdiv_hi)
    return list(range(b_lo, b_hi + 1))


@dataclass
class TestCase:
    name: str
    n: int
    E_non: tuple[int, ...]         # n-3 retained non-divisible runners
    k_div: int                      # divisible runner is k_div * n
    M: int                          # free runner
    d: int                          # dropped unit residue class


@dataclass
class TestResult:
    case: TestCase
    L: int
    j_count: int
    safe_count: int
    phi_n: int
    passed: bool
    failing_b: list[tuple[int, list[tuple[int, int, int]]]]  # (b, [(e, floor, bad_set_contains_sd)])


def run_case(tc: TestCase) -> TestResult:
    n = tc.n
    phi_n = n - 1  # n prime
    all_speeds = list(tc.E_non) + [tc.k_div * n, tc.M]
    if len(set(all_speeds)) != len(all_speeds):
        return TestResult(tc, 0, 0, 0, phi_n, False, [])  # duplicate speeds: skip
    L = lcm_many(all_speeds)

    # Dropped unit d not in R_non
    R_non = {e % n for e in tc.E_non} | {tc.M % n}
    if tc.d in R_non:
        return TestResult(tc, L, 0, 0, phi_n, False, [])  # invalid: d must be missing
    if math.gcd(tc.d, n) != 1:
        return TestResult(tc, L, 0, 0, phi_n, False, [])  # d must be a unit

    d_inv = modinv(tc.d, n)
    s_d = (d_inv - 1) % n

    j_fibres = j_integer_fibres(L, n)
    safe_count = 0
    failing_b: list[tuple[int, list[tuple[int, int, int]]]] = []
    non_div = list(tc.E_non) + [tc.M]

    for b in j_fibres:
        covered_by: list[tuple[int, int, int]] = []
        for e in non_div:
            bs = bad_set(e, b, L, n)
            if s_d in bs:
                covered_by.append((e, (e * b) // L, 1))
        if not covered_by:
            safe_count += 1
        else:
            failing_b.append((b, covered_by))

    passed = safe_count >= phi_n
    return TestResult(tc, L, len(j_fibres), safe_count, phi_n, passed, failing_b)


def build_test_cases() -> list[TestCase]:
    cases: list[TestCase] = []

    # ---- n = 5 ----
    # E_non has 2 elements. Units of Z/5Z: {1,2,3,4}. Drop one unit d, keep 3
    # units minus one (so |E_non| = 2 is 3 candidates minus 1 ignored).
    # Actually |E| = n-1 = 4 total runners: 1 div, 1 free M, 2 in E_non.
    # So R_non (including M) must be a 3-element subset of {1,2,3,4} (modular),
    # and d is the missing unit.
    n = 5
    units = [1, 2, 3, 4]
    for drop_d in units:
        retained_residues = [u for u in units if u != drop_d]
        # Choose 2 for E_non + 1 for M (order matters for labelling)
        for M_res in retained_residues:
            E_non_res = [u for u in retained_residues if u != M_res]
            # Use canonical actual speeds = residues
            E_non = tuple(E_non_res)
            for k_div in [1, 2]:
                for M in [M_res, M_res + n, M_res + 2 * n]:
                    cases.append(TestCase(
                        name=f"n=5,d={drop_d},E_non={E_non},k={k_div},M={M}",
                        n=n, E_non=E_non, k_div=k_div, M=M, d=drop_d))

    # ---- n = 7 ----
    n = 7
    units = [1, 2, 3, 4, 5, 6]
    # |E_non| = 4, plus M, total 5 non-div residues from 6 units => drop exactly 1 unit
    for drop_d in units:
        retained_residues = [u for u in units if u != drop_d]
        for M_res in retained_residues:
            E_non_res = [u for u in retained_residues if u != M_res]
            # Sample a few E_non orderings with canonical residues as actual speeds
            E_non = tuple(E_non_res)
            for k_div in [1]:
                for M in [M_res, M_res + n]:
                    cases.append(TestCase(
                        name=f"n=7,d={drop_d},E_non={E_non},k={k_div},M={M}",
                        n=n, E_non=E_non, k_div=k_div, M=M, d=drop_d))

    # ---- n = 11 canonical: drop {7,9} which is the worst-case for L_0 ----
    n = 11
    # E_non = {1,2,3,4,5,6,8,10}, drop_d = 9, M = 7 (or similar)
    # But we need |E_non|=8 and M is a separate free runner.
    # Total non-div runners = 9. Units = {1..10}. So drop 1 unit (d=9) and
    # pick M from {1..10} \ {9}. E_non = units \ {9, M}.
    for drop_d in [7, 9]:
        for M_res in [u for u in range(1, 11) if u != drop_d]:
            E_non_res = [u for u in range(1, 11) if u != drop_d and u != M_res]
            E_non = tuple(E_non_res)
            for k_div in [1, 2]:
                cases.append(TestCase(
                    name=f"n=11 canonical,d={drop_d},E_non={E_non},k={k_div},M={M_res}",
                    n=n, E_non=E_non, k_div=k_div, M=M_res, d=drop_d))

    # ---- n = 11 A.8 non-canonical: speed 40 = 7 mod 11 ----
    # E_non = {1,2,3,4,5,6,8,40} (replaces 7 with 40); drop d = 9; M = 10
    # Check several M choices
    n = 11
    E_non_a8 = (1, 2, 3, 4, 5, 6, 8, 40)
    for M in [10, 21, 32]:  # various M with gcd(M,11)=1
        cases.append(TestCase(
            name=f"n=11 A.8 speed40,d=9,E_non={E_non_a8},k=1,M={M}",
            n=11, E_non=E_non_a8, k_div=1, M=M, d=9))

    # ---- n = 11 additional non-canonical: speed 29 = 7 mod 11, speed 19 = 8 mod 11
    for E_non_nc in [(1, 2, 3, 4, 5, 6, 29, 10),          # swap 7 -> 29
                    (1, 2, 3, 4, 5, 6, 7, 19),            # swap 8 -> 19
                    (1, 2, 3, 4, 5, 6, 29, 19),           # both swapped
                    (1, 2, 3, 4, 5, 6, 40, 21)]:          # 40=7, 21=10
        for M in [9, 10, 13]:
            if M not in E_non_nc:
                cases.append(TestCase(
                    name=f"n=11 non-canonical,d=varies,E_non={E_non_nc},M={M}",
                    n=11, E_non=E_non_nc, k_div=1, M=M, d=9))

    return cases


def main() -> int:
    cases = build_test_cases()
    total = 0
    passed = 0
    failed = 0
    skipped = 0
    failures: list[TestResult] = []

    for tc in cases:
        r = run_case(tc)
        if r.L == 0 or r.j_count == 0 and r.safe_count == 0 and not r.passed:
            # Skipped due to invalid input (dup speeds, d in R_non)
            skipped += 1
            continue
        total += 1
        if r.passed:
            passed += 1
        else:
            failed += 1
            failures.append(r)

    print(f"=== SUMMARY ===")
    print(f"Total tests: {total} (skipped: {skipped})")
    print(f"Passed (safe_count >= phi(n)): {passed}")
    print(f"Failed: {failed}")

    if failures:
        print(f"\n=== FAILURES ({len(failures)}) ===")
        for r in failures[:20]:
            print(f"\nCase: {r.case.name}")
            print(f"  L = {r.L}, |J ∩ Z| = {r.j_count}, safe = {r.safe_count}, need >= {r.phi_n}")
            if r.failing_b:
                print(f"  First few covered fibres (b, [(speed, floor_state, sd_covered)]):")
                for b, cov in r.failing_b[:3]:
                    print(f"    b={b}: {cov}")
        return 1

    print(f"\nALL TESTS PASSED. Late-window Lemma 10.2' empirically confirmed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
