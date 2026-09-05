#!/usr/bin/env python3
"""
RIDE V18 - Cycle-manifold RSN planner.

This is the tighter alteration of the TSP idea:

  - Do not search arbitrary permutations.
  - Move onto the exact cycle manifold of the target permutation.
  - Score cycles by "stress" (span / displacement).
  - Pick a deterministic pivot inside each stressed cycle.
  - Emit the exact transposition sequence for that cycle.

Why this matters:
  Once the target permutation is known at the encoder, the ordering problem is
  no longer NP-hard. The cycle manifold gives an exact linear-time plan:
    each accepted perturbation raises cycle count by 1
    each accepted perturbation lowers mile by 1

This still does not solve the decoder-shared orbit by itself. But it identifies
the correct encoder-side reduction: RSN should work on cycles, not on an
arbitrary global PRNG walk.
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
MIAI = Path("/Users/trentpalelei/MIAI")
for candidate in (HERE, MIAI):
    candidate_str = str(candidate)
    if candidate.exists() and candidate_str not in sys.path:
        sys.path.insert(0, candidate_str)

from ride_v12_kmanifold_probe import (
    binary_to_decimal_lossless,
    construct_pivot_seed,
    digit_counts,
    iterate_to_fixed,
    nearest_thermo_params,
    thermo_counts_from_params,
)
from ride_v13_canterbury_recipe_bench import (
    build_perm_target_to_source,
    deterministic_frequency_patch,
    permutation_cycle_mile,
    str_to_digits,
)
from ride_v2_kpog_encoder import apply_swaps, decompose_cycles


def materialise_source_and_target(raw: bytes) -> tuple[list[int], list[int], tuple[int, int, int, int], int]:
    decimal = binary_to_decimal_lossless(raw)
    target_counts = digit_counts(decimal)
    target_digits = list(str_to_digits(decimal))

    v0, a, b, v9, l1 = nearest_thermo_params(target_counts)
    thermo_counts = thermo_counts_from_params(v0, a, b, v9)
    seed = construct_pivot_seed(thermo_counts)
    k_constant, _steps, status = iterate_to_fixed(seed, max_iter=30)
    if k_constant is None:
        raise ValueError(f"K materialisation failed with status={status}")
    k_digits = list(str_to_digits(k_constant))
    patched_source, _delta, _edits = deterministic_frequency_patch(bytearray(k_digits), target_counts)
    return list(patched_source), target_digits, (v0, a, b, v9), l1


def cycle_stress(cycle: list[int], perm: list[int]) -> tuple[int, int, int]:
    displacement = sum(abs(index - perm[index]) for index in cycle)
    span = max(cycle) - min(cycle)
    length = len(cycle)
    return displacement, span, length


def choose_cycle_pivot(cycle: list[int], perm: list[int]) -> int:
    return min(
        cycle,
        key=lambda index: (-abs(index - perm[index]), index),
    )


def rotate_cycle_to_pivot(cycle: list[int], pivot: int) -> list[int]:
    pivot_index = cycle.index(pivot)
    return cycle[pivot_index:] + cycle[:pivot_index]


def cycle_to_swaps(cycle: list[int], perm: list[int]) -> list[tuple[int, int]]:
    """
    Deterministic exact transposition schedule for one cycle.
    """
    if len(cycle) <= 1:
        return []
    pivot = choose_cycle_pivot(cycle, perm)
    rotated = rotate_cycle_to_pivot(cycle, pivot)
    return [(rotated[0], rotated[i]) for i in range(len(rotated) - 1, 0, -1)]


def build_rsn_cycle_plan(perm: list[int]) -> dict:
    cycles = decompose_cycles(perm)
    non_trivial = [cycle for cycle in cycles if len(cycle) > 1]

    scored_cycles: list[tuple[tuple[int, int, int, int], list[int]]] = []
    for cycle in non_trivial:
        displacement, span, length = cycle_stress(cycle, perm)
        pivot = choose_cycle_pivot(cycle, perm)
        scored_cycles.append(((displacement, span, length, -pivot), cycle))

    scored_cycles.sort(reverse=True)

    swaps: list[tuple[int, int]] = []
    cycle_meta: list[dict] = []
    for score, cycle in scored_cycles:
        displacement, span, length, neg_pivot = score
        cycle_swaps = cycle_to_swaps(cycle, perm)
        swaps.extend(cycle_swaps)
        cycle_meta.append(
            {
                "length": length,
                "span": span,
                "displacement": displacement,
                "pivot": -neg_pivot,
                "swaps": len(cycle_swaps),
            }
        )

    return {
        "cycles": cycles,
        "non_trivial": len(non_trivial),
        "swaps": swaps,
        "cycle_meta": cycle_meta,
    }


def run_case(path: Path) -> bool:
    raw = path.read_bytes()
    print(f"\n{'=' * 72}")
    print(f"  Cycle-manifold RSN case: {path.name}")
    print(f"{'=' * 72}")
    print(f"  Raw bytes: {len(raw):,}")

    t0 = time.perf_counter()
    source_digits, target_digits, params, l1 = materialise_source_and_target(raw)
    prep_time = time.perf_counter() - t0

    t1 = time.perf_counter()
    perm = list(build_perm_target_to_source(bytearray(target_digits), bytearray(source_digits)))
    mile, cycles = permutation_cycle_mile(perm)
    plan = build_rsn_cycle_plan(perm)
    plan_time = time.perf_counter() - t1

    t2 = time.perf_counter()
    reconstructed = apply_swaps(source_digits, plan["swaps"])
    verify_time = time.perf_counter() - t2
    ok = reconstructed == target_digits

    print(f"  K params: v0={params[0]:,} a={params[1]:,} b={params[2]:,} v9={params[3]:,}")
    print(f"  Frequency delta L1: {l1:,}")
    print(f"  Prep time: {prep_time:.2f}s")
    print(f"  Mile (min transpositions): {mile:,}")
    print(f"  Total cycles: {cycles:,}")
    print(f"  Non-trivial cycles: {plan['non_trivial']:,}")
    print(f"  Planned perturbations: {len(plan['swaps']):,}")
    print(f"  Plan time: {plan_time:.2f}s")
    print(f"  Replay verify time: {verify_time:.2f}s")
    print(f"  Exact reconstruction: {'YES' if ok else 'NO'}")

    if plan["cycle_meta"]:
        first = plan["cycle_meta"][0]
        print(
            f"  Most stressed cycle: len={first['length']:,} span={first['span']:,} "
            f"disp={first['displacement']:,} pivot={first['pivot']:,} swaps={first['swaps']:,}"
        )
        top5 = plan["cycle_meta"][:5]
        avg_top_span = sum(item["span"] for item in top5) / len(top5)
        avg_top_len = sum(item["length"] for item in top5) / len(top5)
        print(f"  Top-5 avg span: {avg_top_span:,.1f}  avg len: {avg_top_len:,.1f}")

    return ok


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Cycle-manifold RSN planner")
    parser.add_argument("file", help="Whole file to test")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V18 - CYCLE-MANIFOLD RSN PLANNER                      ║")
    print("║  stressed cycles -> exact perturbation schedule             ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    ok = run_case(Path(args.file).expanduser())
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
