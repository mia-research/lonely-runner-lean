from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import combinations
from math import gcd, lcm


def gcd_all(values: tuple[int, ...]) -> int:
    g = 0
    for value in values:
        g = gcd(g, value)
    return g


def inv_mod(a: int, n: int) -> int:
    return pow(a, -1, n)


def bad_set(e: int, b: int, L: int, n: int) -> set[int]:
    t = (e * b) // L
    rho = e % n
    out: set[int] = set()
    for r in range(n):
        if (rho * r + t) % n == 0:
            out.add(r)
        if (rho * r + t + 1) % n == 0:
            out.add(r)
    return out


def coverage_union(E_non: list[int], b: int, L: int, n: int) -> set[int]:
    union: set[int] = set()
    for e in E_non:
        union |= bad_set(e, b, L, n)
    return union


@dataclass
class Patcher:
    e: int
    q: int
    rho: int
    is_unit: bool
    covers_via_qd: bool
    covers_via_q1d: bool


@dataclass
class Instance:
    n: int
    E: tuple[int, ...]
    L: int
    b0: int
    d: int
    r_d: int
    patchers: list[Patcher]
    fully_covered_at_b0: bool
    some_patcher_has_later_safe_reset: bool
    first_safe_b: int | None
    first_safe_b_has_patcher_reset: bool


def retained_nondivisible(E: tuple[int, ...], n: int) -> list[int]:
    return [e for e in E if e % n != 0]


def patchers_of_target(E_non: list[int], b0: int, L: int, n: int, d: int) -> tuple[int, list[Patcher]]:
    r_d = (-inv_mod(d, n)) % n
    out: list[Patcher] = []
    for e in E_non:
        if r_d not in bad_set(e, b0, L, n):
            continue
        rho = e % n
        q = e // n
        out.append(
            Patcher(
                e=e,
                q=q,
                rho=rho,
                is_unit=(gcd(rho, n) == 1),
                covers_via_qd=((rho - q * d) % n == 0),
                covers_via_q1d=((rho - (q + 1) * d) % n == 0),
            )
        )
    return r_d, out


def reset_times_in_window(e: int, b0: int, L: int, n: int) -> list[int]:
    out: list[int] = []
    lower_m = (e * b0) // L + 1
    upper_b = ((n - 1) * L) // n
    for m in range(lower_m, e):
        if (m * L) % e != 0:
            continue
        b = (m * L) // e
        if b0 <= b <= upper_b:
            out.append(b)
    return out


def first_safe_b(E_non: list[int], b0: int, L: int, n: int) -> int | None:
    upper_b = ((n - 1) * L) // n
    for b in range(b0, upper_b + 1):
        if len(coverage_union(E_non, b, L, n)) < n:
            return b
    return None


def analyze_instance(E: tuple[int, ...], n: int, d: int) -> Instance:
    L = 1
    for e in E:
        L = lcm(L, e)
    b0 = L // n
    E_non = retained_nondivisible(E, n)
    union0 = coverage_union(E_non, b0, L, n)
    r_d, patchers = patchers_of_target(E_non, b0, L, n, d)

    later_safe_reset = False
    for patcher in patchers:
        for b in reset_times_in_window(patcher.e, b0, L, n):
            if len(coverage_union(E_non, b, L, n)) < n:
                later_safe_reset = True
                break
        if later_safe_reset:
            break

    safe_b = first_safe_b(E_non, b0, L, n)
    patcher_reset_at_first_safe = False
    if safe_b is not None:
        for patcher in patchers:
            if safe_b in reset_times_in_window(patcher.e, b0, L, n):
                patcher_reset_at_first_safe = True
                break

    return Instance(
        n=n,
        E=E,
        L=L,
        b0=b0,
        d=d,
        r_d=r_d,
        patchers=patchers,
        fully_covered_at_b0=(len(union0) == n),
        some_patcher_has_later_safe_reset=later_safe_reset,
        first_safe_b=safe_b,
        first_safe_b_has_patcher_reset=patcher_reset_at_first_safe,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-n", type=int, default=4)
    parser.add_argument("--max-n", type=int, default=8)
    parser.add_argument("--speed-mult", type=int, default=3)
    parser.add_argument("--show-no-reset", action="store_true")
    parser.add_argument("--show-limit", type=int, default=8)
    args = parser.parse_args()

    for n in range(args.min_n, args.max_n + 1):
        nums = list(range(1, args.speed_mult * n + 1))
        total_missing = 0
        fully_covered = 0
        patcher_congruence_failures = 0
        unit_patcher_instances = 0
        nonunit_patcher_instances = 0
        mixed_patcher_instances = 0
        later_safe_reset = 0
        first_safe_has_patcher_reset = 0
        no_safe_b = 0
        examples: list[Instance] = []
        no_reset_examples: list[Instance] = []

        for E in combinations(nums, n - 1):
            if gcd_all(E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue

            E_non = retained_nondivisible(E, n)
            R_non = {e % n for e in E_non}
            units = [u for u in range(1, n) if gcd(u, n) == 1]
            missing_units = [d for d in units if d not in R_non]

            for d in missing_units:
                total_missing += 1
                inst = analyze_instance(E, n, d)
                if not inst.fully_covered_at_b0:
                    continue

                fully_covered += 1
                has_unit = any(p.is_unit for p in inst.patchers)
                has_nonunit = any(not p.is_unit for p in inst.patchers)
                if has_unit and has_nonunit:
                    mixed_patcher_instances += 1
                elif has_unit:
                    unit_patcher_instances += 1
                elif has_nonunit:
                    nonunit_patcher_instances += 1

                for patcher in inst.patchers:
                    if not (patcher.covers_via_qd or patcher.covers_via_q1d):
                        patcher_congruence_failures += 1

                if inst.some_patcher_has_later_safe_reset:
                    later_safe_reset += 1
                elif len(no_reset_examples) < args.show_limit:
                    no_reset_examples.append(inst)
                if inst.first_safe_b is None:
                    no_safe_b += 1
                elif inst.first_safe_b_has_patcher_reset:
                    first_safe_has_patcher_reset += 1
                elif len(examples) < args.show_limit:
                    examples.append(inst)

        print(f"n={n}")
        print(f"  total missing-unit instances: {total_missing}")
        print(f"  fully covered at b0: {fully_covered}")
        print(f"  unit-only patcher instances: {unit_patcher_instances}")
        print(f"  nonunit-only patcher instances: {nonunit_patcher_instances}")
        print(f"  mixed patcher instances: {mixed_patcher_instances}")
        print(f"  patcher congruence failures: {patcher_congruence_failures}")
        if fully_covered:
            print(f"  some patcher has later safe reset: {later_safe_reset}/{fully_covered}")
            print(f"  first safe b is a patcher reset: {first_safe_has_patcher_reset}/{fully_covered - no_safe_b}")
            print(f"  instances with no safe b in B_div: {no_safe_b}")

        for inst in examples:
            print(
                "  non-patcher-first-safe example:",
                {
                    "E": inst.E,
                    "d": inst.d,
                    "r_d": inst.r_d,
                    "b0": inst.b0,
                    "first_safe_b": inst.first_safe_b,
                    "patchers": [
                        {
                            "e": p.e,
                            "rho": p.rho,
                            "unit": p.is_unit,
                            "qd": p.covers_via_qd,
                            "q1d": p.covers_via_q1d,
                        }
                        for p in inst.patchers
                    ],
                },
            )
        if args.show_no_reset:
            for inst in no_reset_examples:
                print(
                    "  no-patcher-reset example:",
                    {
                        "E": inst.E,
                        "d": inst.d,
                        "r_d": inst.r_d,
                        "b0": inst.b0,
                        "first_safe_b": inst.first_safe_b,
                        "patchers": [
                            {
                                "e": p.e,
                                "rho": p.rho,
                                "unit": p.is_unit,
                                "qd": p.covers_via_qd,
                                "q1d": p.covers_via_q1d,
                            }
                            for p in inst.patchers
                        ],
                    },
                )


if __name__ == "__main__":
    main()
