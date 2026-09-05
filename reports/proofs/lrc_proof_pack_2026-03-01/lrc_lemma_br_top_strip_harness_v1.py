"""
lrc_lemma_br_top_strip_harness_v1.py

Search harness for the Lemma BR window-maintenance reduction.

This script works in the prime/unit branch with 1 in E_non and focuses on the
S_0 candidates supplied by the large-runner pigeonhole argument.

For each candidate residue r with unique large excluder e* > n, it computes:
  - the zone of e* at b_lo
  - the exact arrival arr(e*, r)
  - the exact per-runner window blockers
  - the affine tau-index top strips whose avoidance is equivalent to
    window maintenance

It can analyze a single tuple or run a bounded sweep.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import combinations
from math import gcd
from typing import Iterable, Sequence


def lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def lcm_list(values: Sequence[int]) -> int:
    out = 1
    for value in values:
        out = lcm(out, value)
    return out


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    k = 3
    while k * k <= n:
        if n % k == 0:
            return False
        k += 2
    return True


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def safe_set(e: int, b: int, L: int, n: int) -> set[int]:
    N = n * L
    return {
        a
        for a in range(n)
        if L <= (e * (a * L + b)) % N <= (n - 1) * L
    }


def x0_value(e: int, r: int, b_lo: int, L: int, n: int) -> int:
    return (e * (r * L + b_lo)) % (n * L)


def tau_index(e: int, r: int, n: int) -> int:
    q, s = divmod(e, n)
    return (q + s * r) % n


def zone_at_blo(e: int, r: int, n: int) -> str:
    tau = tau_index(e, r, n)
    if tau == 0:
        return "lower"
    if tau == n - 1:
        return "upper"
    return "safe"


def arrival_time(e: int, r: int, b_lo: int, L: int, n: int) -> int:
    x = x0_value(e, r, b_lo, L, n)
    N = n * L
    if L <= x <= (n - 1) * L:
        return 0
    gap = (L - x) if x < L else (N - x + L)
    assert gap % e == 0
    return gap // e


def window_from_blo(e: int, r: int, b_lo: int, L: int, n: int) -> int | None:
    x = x0_value(e, r, b_lo, L, n)
    if not (L <= x <= (n - 1) * L):
        return None
    return ((n - 1) * L - x) // e


def zone_arrival_numerator(e_star: int, zone: str, n: int) -> int:
    _, s_star = divmod(e_star, n)
    if zone == "lower":
        return n - s_star
    if zone == "upper":
        return 2 * n - s_star
    raise ValueError(f"unexpected zone: {zone}")


def strip_threshold(e: int, e_star: int, zone_num: int, n: int) -> int:
    _, s = divmod(e, n)
    return ceil_div(e * zone_num + e_star * s, n * e_star)


def forbidden_tau_strip(e: int, e_star: int, zone_num: int, n: int) -> tuple[int, int] | None:
    c_e = strip_threshold(e, e_star, zone_num, n)
    if c_e <= 1:
        return None
    start = n - c_e
    end = n - 2
    if start > end:
        return None
    return start, end


@dataclass
class Blocker:
    runner: int
    tau: int
    threshold: int
    strip: tuple[int, int] | None
    window: int


@dataclass
class Candidate:
    residue: int
    excluder: int
    zone: str
    arrival: int
    budget_ok: bool
    valid: bool
    blockers: list[Blocker]


@dataclass
class TupleAnalysis:
    n: int
    e_non: tuple[int, ...]
    L: int
    b_lo: int
    budget: float
    case_b: bool
    all_unique_candidates: list[Candidate]
    low_multiplicity_candidates: list["LowMultiplicityCandidate"]
    s0: list[int]
    s0_unique_large_candidates: list[Candidate]


@dataclass
class LowMultiplicityCandidate:
    residue: int
    excluders: tuple[int, ...]
    arrival_cap: int
    budget_ok: bool
    valid: bool
    blockers: list[tuple[int, int, int]]


def candidate_for_residue(
    n: int,
    e_non: Sequence[int],
    L: int,
    b_lo: int,
    budget: float,
    safe_sets: dict[int, set[int]],
    r: int,
    unique_large_only: bool,
) -> Candidate | None:
    excluders = [e for e in e_non if r not in safe_sets[e]]
    if len(excluders) != 1:
        return None

    e_star = excluders[0]
    if unique_large_only and e_star <= n:
        return None

    zone = zone_at_blo(e_star, r, n)
    if zone not in {"lower", "upper"}:
        return None

    zone_num = zone_arrival_numerator(e_star, zone, n)
    arrival = arrival_time(e_star, r, b_lo, L, n)
    expected = L * zone_num // (n * e_star)
    assert arrival == expected

    blockers: list[Blocker] = []
    for e in e_non:
        if e == e_star:
            continue
        if r not in safe_sets[e]:
            continue

        tau = tau_index(e, r, n)
        window = window_from_blo(e, r, b_lo, L, n)
        assert window is not None

        threshold = strip_threshold(e, e_star, zone_num, n)
        strip = forbidden_tau_strip(e, e_star, zone_num, n)
        fails_exact = window < arrival
        fails_strip = strip is not None and strip[0] <= tau <= strip[1]
        assert fails_exact == fails_strip

        if fails_exact:
            blockers.append(
                Blocker(
                    runner=e,
                    tau=tau,
                    threshold=threshold,
                    strip=strip,
                    window=window,
                )
            )

    return Candidate(
        residue=r,
        excluder=e_star,
        zone=zone,
        arrival=arrival,
        budget_ok=arrival <= budget,
        valid=(arrival <= budget and not blockers),
        blockers=blockers,
    )


def analyze_tuple(n: int, e_non: Sequence[int]) -> TupleAnalysis:
    e_non = tuple(sorted(e_non))
    if 1 not in e_non:
        raise ValueError("tuple analysis requires 1 in E_non for the S_0 branch")
    if not is_prime(n):
        raise ValueError("tuple analysis is scoped to prime n")
    if any(gcd(e, n) != 1 for e in e_non):
        raise ValueError("tuple analysis requires all non-divisor runners to be units")

    e_all = list(e_non) + [n]
    if gcd(*e_all) != 1:
        raise ValueError("tuple is not gcd-1")

    L = lcm_list(e_all)
    b_lo = L // n
    budget = (n - 2) * (L - n) / (2 * n)
    safe_sets = {e: safe_set(e, b_lo, L, n) for e in e_non}

    ab_lo = set(range(n))
    for e in e_non:
        ab_lo &= safe_sets[e]
    case_b = not ab_lo

    if not case_b:
        return TupleAnalysis(
            n=n,
            e_non=e_non,
            L=L,
            b_lo=b_lo,
            budget=budget,
            case_b=False,
            all_unique_candidates=[],
            low_multiplicity_candidates=[],
            s0=[],
            s0_unique_large_candidates=[],
        )

    all_unique_candidates = []
    for r in range(n):
        row = candidate_for_residue(n, e_non, L, b_lo, budget, safe_sets, r, unique_large_only=False)
        if row is not None:
            all_unique_candidates.append(row)

    low_multiplicity_candidates: list[LowMultiplicityCandidate] = []
    for r in range(n):
        excluders = [e for e in e_non if r not in safe_sets[e]]
        if not (1 <= len(excluders) <= 2):
            continue
        cap = max(arrival_time(e, r, b_lo, L, n) for e in excluders)
        blockers = []
        for e in e_non:
            if e in excluders:
                continue
            if r not in safe_sets[e]:
                continue
            tau = tau_index(e, r, n)
            window = window_from_blo(e, r, b_lo, L, n)
            assert window is not None
            if window < cap:
                blockers.append((e, tau, window))
        low_multiplicity_candidates.append(
            LowMultiplicityCandidate(
                residue=r,
                excluders=tuple(excluders),
                arrival_cap=cap,
                budget_ok=(cap <= budget),
                valid=(cap <= budget and not blockers),
                blockers=blockers,
            )
        )

    small_runners = [e for e in e_non if e < n]
    a_small = {
        r
        for r in range(1, n - 1)
        if any(r not in safe_sets[e] for e in small_runners)
    }
    s0 = [r for r in range(1, n - 1) if r not in a_small]

    s0_unique_large_candidates = []
    for r in s0:
        row = candidate_for_residue(n, e_non, L, b_lo, budget, safe_sets, r, unique_large_only=True)
        if row is not None:
            s0_unique_large_candidates.append(row)

    return TupleAnalysis(
        n=n,
        e_non=e_non,
        L=L,
        b_lo=b_lo,
        budget=budget,
        case_b=True,
        all_unique_candidates=all_unique_candidates,
        low_multiplicity_candidates=low_multiplicity_candidates,
        s0=s0,
        s0_unique_large_candidates=s0_unique_large_candidates,
    )


def print_candidate(candidate: Candidate) -> None:
    status = "VALID" if candidate.valid else "BLOCKED"
    print(
        f"    r={candidate.residue}: e*={candidate.excluder} "
        f"zone={candidate.zone} arr={candidate.arrival} "
        f"budget_ok={candidate.budget_ok} status={status}"
    )
    for blocker in candidate.blockers:
        print(
            f"      blocker e={blocker.runner} tau={blocker.tau} "
            f"threshold={blocker.threshold} strip={blocker.strip} "
            f"window={blocker.window}"
        )


def run_single(n: int, tuple_arg: str) -> None:
    e_non = tuple(sorted(int(x) for x in tuple_arg.split(",") if x.strip()))
    result = analyze_tuple(n, e_non)

    print("=" * 72)
    print(f"n={result.n}, E_non={result.e_non}, L={result.L}, b_lo={result.b_lo}")
    print(f"budget={result.budget:.3f}, Case B={result.case_b}")
    if not result.case_b:
        return

    print(f"S0={result.s0}")
    print("\nAll unique-excluder residues:")
    for candidate in result.all_unique_candidates:
        print_candidate(candidate)

    print("\nLow-multiplicity residues (1 or 2 excluders):")
    for candidate in result.low_multiplicity_candidates:
        status = "VALID" if candidate.valid else "BLOCKED"
        print(
            f"    r={candidate.residue}: excluders={candidate.excluders} "
            f"cap={candidate.arrival_cap} budget_ok={candidate.budget_ok} status={status}"
        )
        for runner, tau, window in candidate.blockers:
            print(f"      blocker e={runner} tau={tau} window={window}")

    print("\nS0 residues with unique large excluder:")
    for candidate in result.s0_unique_large_candidates:
        print_candidate(candidate)


def sweep_tuples(
    n_values: Iterable[int],
    max_e_factor: int,
    max_per_n: int,
) -> None:
    total_case_b = 0
    tuples_with_valid_s0 = 0
    tuples_with_only_blocked_s0 = 0
    tuples_with_valid_low_mult = 0
    total_s0_candidates = 0
    valid_s0_candidates = 0

    for n in n_values:
        if not is_prime(n):
            continue

        unit_speeds = [e for e in range(1, max_e_factor * n + 1) if e != n and gcd(e, n) == 1]
        checked = 0
        n_case_b = 0
        n_valid_tuples = 0
        n_blocked_tuples = 0
        n_valid_low_mult = 0

        for combo in combinations(unit_speeds, n - 2):
            if checked >= max_per_n:
                break
            if 1 not in combo:
                continue

            result = analyze_tuple(n, combo)
            checked += 1
            if not result.case_b:
                continue

            n_case_b += 1
            total_case_b += 1
            total_s0_candidates += len(result.s0_unique_large_candidates)
            valid_here = [row for row in result.s0_unique_large_candidates if row.valid]
            valid_s0_candidates += len(valid_here)
            if any(row.valid for row in result.low_multiplicity_candidates):
                n_valid_low_mult += 1
                tuples_with_valid_low_mult += 1

            if valid_here:
                n_valid_tuples += 1
                tuples_with_valid_s0 += 1
            elif result.s0_unique_large_candidates:
                n_blocked_tuples += 1
                tuples_with_only_blocked_s0 += 1

        print(
            f"n={n}: checked={checked}, caseB={n_case_b}, "
            f"tuples_with_valid_S0={n_valid_tuples}, "
            f"tuples_with_only_blocked_S0={n_blocked_tuples}, "
            f"tuples_with_valid_low_mult={n_valid_low_mult}"
        )

    print("\nSummary:")
    print(f"  Case B tuples: {total_case_b}")
    print(f"  Total S0 unique-large candidates: {total_s0_candidates}")
    print(f"  Valid S0 candidates: {valid_s0_candidates}")
    print(f"  Tuples with at least one valid S0 candidate: {tuples_with_valid_s0}")
    print(f"  Tuples with only blocked S0 candidates: {tuples_with_only_blocked_s0}")
    print(f"  Tuples with a valid 1/2-excluder candidate: {tuples_with_valid_low_mult}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Lemma BR top-strip window-maintenance harness")
    parser.add_argument("--n", type=int, help="single n value")
    parser.add_argument("--tuple", dest="tuple_arg", help="comma-separated E_non tuple for single analysis")
    parser.add_argument("--n-min", type=int, default=5, help="minimum n for sweep")
    parser.add_argument("--n-max", type=int, default=11, help="maximum n for sweep")
    parser.add_argument("--max-e-factor", type=int, default=4, help="search bound e <= factor * n")
    parser.add_argument("--max-per-n", type=int, default=150, help="max tuples per n in sweep")
    args = parser.parse_args()

    if args.tuple_arg:
        if args.n is None:
            raise SystemExit("--tuple requires --n")
        run_single(args.n, args.tuple_arg)
        return

    sweep_tuples(range(args.n_min, args.n_max + 1), args.max_e_factor, args.max_per_n)


if __name__ == "__main__":
    main()
