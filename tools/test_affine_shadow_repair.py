from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from math import gcd, lcm


def gcd_all(values):
    g = 0
    for v in values:
        g = gcd(g, v)
    return g


def inv_mod(a: int, n: int) -> int:
    return pow(a, -1, n)


def bad_set(e: int, b: int, L: int, n: int) -> set[int]:
    t = (e * b) // L
    rho = e % n
    g = gcd(rho, n)
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
class ShadowData:
    e: int
    q: int
    rho: int
    mode: str
    companion: int
    next_reset_b: int
    safe_at_next_reset: bool
    dropped_residue_uncovered: bool


@dataclass
class TupleResult:
    E: tuple[int, ...]
    n: int
    L: int
    d: int
    r_d: int
    b0: int
    uncovered_at_b0: bool
    covered_by_nonunit_at_b0: bool
    shadowers: list[ShadowData]
    some_next_reset_safe: bool
    some_next_reset_dropped_uncovered: bool
    some_later_reset_safe: bool


def analyze_tuple(E: tuple[int, ...], n: int) -> list[TupleResult]:
    L = 1
    for e in E:
        L = lcm(L, e)
    b0 = L // n
    E_non = [e for e in E if e % n != 0]
    R_non = {e % n for e in E_non}
    units = [u for u in range(1, n) if gcd(u, n) == 1]
    missing_units = [d for d in units if d not in R_non]
    base_union = coverage_union(E_non, b0, L, n)

    out: list[TupleResult] = []
    for d in missing_units:
        r_d = (-inv_mod(d, n)) % n
        shadowers: list[ShadowData] = []
        for e in E_non:
            rho = e % n
            if gcd(rho, n) != 1:
                continue
            q = e // n
            a_low = (-q * inv_mod(rho, n)) % n
            a_high = (-(q + 1) * inv_mod(rho, n)) % n
            if r_d not in {a_low, a_high}:
                continue
            mode = "high" if a_high == r_d else "low"
            companion = a_low if mode == "high" else a_high
            next_reset_b = ((q + 1) * L) // e
            safe_at_next_reset = False
            dropped_uncovered = False
            if b0 <= next_reset_b <= ((n - 1) * L) // n:
                union_next = coverage_union(E_non, next_reset_b, L, n)
                safe_at_next_reset = len(union_next) < n
                old_bad = bad_set(e, b0, L, n)
                new_bad = bad_set(e, next_reset_b, L, n)
                dropped = old_bad - new_bad
                if companion in dropped and companion not in (union_next - new_bad):
                    dropped_uncovered = True
            shadowers.append(
                ShadowData(
                    e=e,
                    q=q,
                    rho=rho,
                    mode=mode,
                    companion=companion,
                    next_reset_b=next_reset_b,
                    safe_at_next_reset=safe_at_next_reset,
                    dropped_residue_uncovered=dropped_uncovered,
                )
            )

        covered_by_nonunit = False
        for e in E_non:
            rho = e % n
            if gcd(rho, n) == 1:
                continue
            if r_d in bad_set(e, b0, L, n):
                covered_by_nonunit = True
                break

        # weaker check: some reset of some shadower yields safe fibre
        some_later_reset_safe = False
        for sh in shadowers:
            e = sh.e
            for m in range((e * b0) // L + 1, e):
                num = m * L
                if num % e != 0:
                    continue
                b = num // e
                if b < b0 or b > ((n - 1) * L) // n:
                    continue
                if len(coverage_union(E_non, b, L, n)) < n:
                    some_later_reset_safe = True
                    break
            if some_later_reset_safe:
                break

        out.append(
            TupleResult(
                E=E,
                n=n,
                L=L,
                d=d,
                r_d=r_d,
                b0=b0,
                uncovered_at_b0=(r_d not in base_union),
                covered_by_nonunit_at_b0=covered_by_nonunit,
                shadowers=shadowers,
                some_next_reset_safe=any(sh.safe_at_next_reset for sh in shadowers),
                some_next_reset_dropped_uncovered=any(
                    sh.dropped_residue_uncovered for sh in shadowers
                ),
                some_later_reset_safe=some_later_reset_safe,
            )
        )
    return out


def main():
    for n in range(4, 9):
        nums = list(range(1, 3 * n + 1))
        total_missing = 0
        b0_uncovered = 0
        affine_shadow_cases = 0
        pure_nonunit_mask_cases = 0
        mixed_cover_cases = 0
        any_affine_cases = 0
        strong_next_reset = 0
        dropped_companion = 0
        weaker_later_reset = 0
        counterexamples: list[TupleResult] = []
        for E in combinations(nums, n - 1):
            if gcd_all(E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue
            for res in analyze_tuple(E, n):
                total_missing += 1
                if res.uncovered_at_b0:
                    b0_uncovered += 1
                    continue
                has_affine = bool(res.shadowers)
                has_nonunit = res.covered_by_nonunit_at_b0
                if has_affine:
                    any_affine_cases += 1
                if has_affine and has_nonunit:
                    mixed_cover_cases += 1
                elif has_affine:
                    affine_shadow_cases += 1
                elif has_nonunit:
                    pure_nonunit_mask_cases += 1

                if has_affine:
                    if res.some_next_reset_safe:
                        strong_next_reset += 1
                    if res.some_next_reset_dropped_uncovered:
                        dropped_companion += 1
                    if res.some_later_reset_safe:
                        weaker_later_reset += 1
                    if (
                        not res.some_next_reset_safe
                        and len(counterexamples) < 5
                    ):
                        counterexamples.append(res)

        print(f"n={n}")
        print(f"  total missing-unit instances: {total_missing}")
        print(f"  uncovered already at b0: {b0_uncovered}")
        print(f"  affine-shadow cases: {affine_shadow_cases}")
        print(f"  pure non-unit mask cases: {pure_nonunit_mask_cases}")
        print(f"  mixed affine+nonunit cover cases: {mixed_cover_cases}")
        if any_affine_cases:
            print(f"  any affine-shadow cases: {any_affine_cases}")
            print(f"  strong next-reset safe: {strong_next_reset}/{any_affine_cases}")
            print(f"  next-reset dropped companion uncovered: {dropped_companion}/{any_affine_cases}")
            print(f"  weaker some-later-reset safe: {weaker_later_reset}/{any_affine_cases}")
        for res in counterexamples:
            print(
                "  counterexample:",
                {
                    "E": res.E,
                    "d": res.d,
                    "r_d": res.r_d,
                    "covered_by_nonunit_at_b0": res.covered_by_nonunit_at_b0,
                    "shadowers": [
                        {
                            "e": sh.e,
                            "mode": sh.mode,
                            "companion": sh.companion,
                            "next_reset_b": sh.next_reset_b,
                            "safe_at_next_reset": sh.safe_at_next_reset,
                            "dropped_residue_uncovered": sh.dropped_residue_uncovered,
                        }
                        for sh in res.shadowers
                    ],
                    "some_later_reset_safe": res.some_later_reset_safe,
                },
            )


if __name__ == "__main__":
    main()
