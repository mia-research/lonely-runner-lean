#!/usr/bin/env python3
"""
RIDE V23 - Cycle-arc compiler.

First concrete implementation of the cycle-native family suggested by V22.

Model:
  - Start from the exact V18 cycle manifold plan.
  - For each stressed cycle, keep the deterministic pivot.
  - View the non-pivot members of the cycle as an active circular ring.
  - Compile the exact pivot-star partner sequence into maximal directed
    extractions along that current ring.

One macro is:
  { start_position, length, direction }

Replay semantics:
  - locate start_position in the current active ring
  - walk `length` active positions in `direction`
  - apply the V18 pivot-star swaps in that order
  - remove those positions from the active ring

This is still an encoder-side exact compiler. The decoder-shared family problem
is not fully solved here because the cycle member set is still assumed known.
But this is the right next test:
  does the exact route compress once expressed as cycle-arc macros rather than
  individual swaps?
"""

from __future__ import annotations

import argparse
import sys
import time
from dataclasses import dataclass
from pathlib import Path

HERE = Path(__file__).resolve().parent
MIAI = Path("/Users/trentpalelei/MIAI")
for candidate in (HERE, MIAI):
    candidate_str = str(candidate)
    if candidate.exists() and candidate_str not in sys.path:
        sys.path.insert(0, candidate_str)

from ride_v13_canterbury_recipe_bench import build_perm_target_to_source, encode_uvarint, permutation_cycle_mile
from ride_v18_cycle_rsn import (
    build_rsn_cycle_plan,
    choose_cycle_pivot,
    cycle_stress,
    cycle_to_swaps,
    materialise_source_and_target,
)
from ride_v2_kpog_encoder import apply_swaps, decompose_cycles


DIR_FWD = 1
DIR_BWD = -1


@dataclass
class ArcMacro:
    start_pos: int
    length: int
    direction: int


@dataclass
class CycleArcPlan:
    pivot: int
    sorted_members: list[int]
    macros: list[ArcMacro]
    swaps: int
    covered_by_long_macros: int
    long_macro_count: int


def score_cycle(cycle: list[int], perm: list[int]) -> tuple[int, int, int, int]:
    displacement, span, length = cycle_stress(cycle, perm)
    pivot = choose_cycle_pivot(cycle, perm)
    return displacement, span, length, -pivot


def sorted_non_trivial_cycles(perm: list[int]) -> list[list[int]]:
    cycles = [cycle for cycle in decompose_cycles(perm) if len(cycle) > 1]
    cycles.sort(key=lambda cycle: score_cycle(cycle, perm), reverse=True)
    return cycles


class ActiveRing:
    def __init__(self, positions: list[int]) -> None:
        self.positions = positions
        self.size = len(positions)
        self.pos_to_index = {position: idx for idx, position in enumerate(positions)}
        self.active = [True] * self.size
        self.next_idx = list(range(1, self.size)) + ([0] if self.size else [])
        self.prev_idx = ([self.size - 1] if self.size else []) + list(range(0, self.size - 1))

    def contains(self, position: int) -> bool:
        idx = self.pos_to_index[position]
        return self.active[idx]

    def successor(self, idx: int) -> int:
        return self.next_idx[idx]

    def predecessor(self, idx: int) -> int:
        return self.prev_idx[idx]

    def remove_indices(self, indices: list[int]) -> None:
        for idx in indices:
            if not self.active[idx]:
                raise ValueError("attempted to remove inactive ring member")
        for idx in indices:
            left = self.prev_idx[idx]
            right = self.next_idx[idx]
            self.next_idx[left] = right
            self.prev_idx[right] = left
            self.active[idx] = False

    def positions_for_macro(self, macro: ArcMacro) -> list[int]:
        if not self.size:
            return []
        start_idx = self.pos_to_index[macro.start_pos]
        if not self.active[start_idx]:
            raise ValueError("macro start position is not active")

        out = [self.positions[start_idx]]
        current = start_idx
        step_fn = self.successor if macro.direction == DIR_FWD else self.predecessor
        for _ in range(1, macro.length):
            current = step_fn(current)
            out.append(self.positions[current])
        return out

    def indices_for_positions(self, positions: list[int]) -> list[int]:
        return [self.pos_to_index[position] for position in positions]


def choose_direction(ring: ActiveRing, partner_sequence: list[int], index: int) -> tuple[int | None, int | None]:
    if index + 1 >= len(partner_sequence):
        return None, None
    current_pos = partner_sequence[index]
    next_pos = partner_sequence[index + 1]
    current_idx = ring.pos_to_index[current_pos]
    succ_idx = ring.successor(current_idx)
    pred_idx = ring.predecessor(current_idx)
    if ring.positions[succ_idx] == next_pos:
        return DIR_FWD, succ_idx
    if ring.positions[pred_idx] == next_pos:
        return DIR_BWD, pred_idx
    return None, None


def compile_cycle_to_arc_macros(cycle: list[int], perm: list[int]) -> CycleArcPlan:
    pivot = choose_cycle_pivot(cycle, perm)
    exact_swaps = cycle_to_swaps(cycle, perm)
    partner_sequence = [partner for _pivot, partner in exact_swaps]
    sorted_members = sorted(position for position in cycle if position != pivot)
    ring = ActiveRing(sorted_members)

    macros: list[ArcMacro] = []
    seq_index = 0
    covered_by_long = 0
    long_macros = 0

    while seq_index < len(partner_sequence):
        start_pos = partner_sequence[seq_index]
        if not ring.contains(start_pos):
            raise ValueError("partner sequence references inactive ring member")

        direction, _next_idx = choose_direction(ring, partner_sequence, seq_index)
        run_len = 1
        if direction is not None:
            current_pos = start_pos
            while seq_index + run_len < len(partner_sequence):
                current_idx = ring.pos_to_index[current_pos]
                expected_idx = ring.successor(current_idx) if direction == DIR_FWD else ring.predecessor(current_idx)
                expected_pos = ring.positions[expected_idx]
                if partner_sequence[seq_index + run_len] != expected_pos:
                    break
                current_pos = expected_pos
                run_len += 1

        macro = ArcMacro(start_pos=start_pos, length=run_len, direction=direction or DIR_FWD)
        macro_positions = ring.positions_for_macro(macro)
        expected_positions = partner_sequence[seq_index : seq_index + run_len]
        if macro_positions != expected_positions:
            raise ValueError("compiled macro does not match exact partner sequence")

        ring.remove_indices(ring.indices_for_positions(macro_positions))
        macros.append(macro)
        if run_len > 1:
            covered_by_long += run_len
            long_macros += 1
        seq_index += run_len

    return CycleArcPlan(
        pivot=pivot,
        sorted_members=sorted_members,
        macros=macros,
        swaps=len(exact_swaps),
        covered_by_long_macros=covered_by_long,
        long_macro_count=long_macros,
    )


def replay_cycle_arc_plan(state: list[int], cycle_plan: CycleArcPlan) -> None:
    ring = ActiveRing(cycle_plan.sorted_members)
    for macro in cycle_plan.macros:
        positions = ring.positions_for_macro(macro)
        for partner in positions:
            state[cycle_plan.pivot], state[partner] = state[partner], state[cycle_plan.pivot]
        ring.remove_indices(ring.indices_for_positions(positions))


def width_bytes(n: int) -> int:
    return max(1, ((max(0, n - 1).bit_length()) + 7) // 8)


def estimate_arc_route_bytes(cycle_plans: list[CycleArcPlan], n_positions: int) -> dict[str, int]:
    width = width_bytes(n_positions)
    cycle_count_bytes = len(encode_uvarint(len(cycle_plans)))
    pivot_bytes = len(cycle_plans) * width
    macro_count_bytes = sum(len(encode_uvarint(len(plan.macros))) for plan in cycle_plans)
    macro_bytes = 0
    for plan in cycle_plans:
        for macro in plan.macros:
            macro_bytes += width
            macro_bytes += len(encode_uvarint(macro.length))
            macro_bytes += 1
    total = cycle_count_bytes + pivot_bytes + macro_count_bytes + macro_bytes
    return {
        "width": width,
        "cycle_count_bytes": cycle_count_bytes,
        "pivot_bytes": pivot_bytes,
        "macro_count_bytes": macro_count_bytes,
        "macro_bytes": macro_bytes,
        "total": total,
    }


def estimate_swap_route_bytes(total_swaps: int, n_positions: int) -> int:
    width = width_bytes(n_positions)
    return 1 + len(encode_uvarint(total_swaps)) + total_swaps * (2 * width)


def estimate_exact_cycle_bytes(cycles: list[list[int]], n_positions: int) -> int:
    width = width_bytes(n_positions)
    total = 1 + 2
    for cycle in cycles:
        if len(cycle) <= 1:
            continue
        total += 2 + len(cycle) * width
    return total


def run_case(path: Path) -> bool:
    raw = path.read_bytes()
    print(f"\n{'=' * 76}")
    print(f"  Cycle-arc compile case: {path.name}")
    print(f"{'=' * 76}")
    print(f"  Raw bytes: {len(raw):,}")

    t0 = time.perf_counter()
    source_digits, target_digits, params, l1 = materialise_source_and_target(raw)
    prep_time = time.perf_counter() - t0

    t1 = time.perf_counter()
    perm = list(build_perm_target_to_source(bytearray(target_digits), bytearray(source_digits)))
    mile, _cycles = permutation_cycle_mile(perm)
    sorted_cycles = sorted_non_trivial_cycles(perm)
    cycle_plans = [compile_cycle_to_arc_macros(cycle, perm) for cycle in sorted_cycles]
    compile_time = time.perf_counter() - t1

    t2 = time.perf_counter()
    reconstructed = list(source_digits)
    for cycle_plan in cycle_plans:
        replay_cycle_arc_plan(reconstructed, cycle_plan)
    verify_time = time.perf_counter() - t2
    ok = reconstructed == target_digits

    total_swaps = sum(plan.swaps for plan in cycle_plans)
    total_macros = sum(len(plan.macros) for plan in cycle_plans)
    long_macro_count = sum(plan.long_macro_count for plan in cycle_plans)
    swaps_covered_by_long = sum(plan.covered_by_long_macros for plan in cycle_plans)
    long_coverage = swaps_covered_by_long / total_swaps if total_swaps else 0.0

    arc_bytes = estimate_arc_route_bytes(cycle_plans, len(target_digits))
    swap_bytes = estimate_swap_route_bytes(total_swaps, len(target_digits))
    exact_cycle_bytes = estimate_exact_cycle_bytes(sorted_cycles, len(target_digits))

    print(f"  K params: v0={params[0]:,} a={params[1]:,} b={params[2]:,} v9={params[3]:,}")
    print(f"  Frequency delta L1: {l1:,}")
    print(f"  Mile / swaps: {mile:,}")
    print(f"  Non-trivial cycles: {len(cycle_plans):,}")
    print(f"  Prep time: {prep_time:.2f}s")
    print(f"  Compile time: {compile_time:.2f}s")
    print(f"  Replay verify time: {verify_time:.2f}s")
    print(f"  Exact reconstruction: {'YES' if ok else 'NO'}")
    print("  Arc route stats:")
    print(f"    macros: {total_macros:,}")
    print(f"    long macros (>1): {long_macro_count:,}")
    print(f"    swaps covered by long macros: {swaps_covered_by_long:,} ({long_coverage:.3%})")
    print(f"    avg swaps per macro: {total_swaps / total_macros if total_macros else 0.0:,.3f}")
    print("  Route bytes:")
    print(f"    arc macros only (cycle set assumed shared): {arc_bytes['total']:,}B")
    print(f"    raw swap route: {swap_bytes:,}B")
    print(f"    exact cycle positions: {exact_cycle_bytes:,}B")

    for index, cycle_plan in enumerate(cycle_plans[:6], start=1):
        cycle_coverage = cycle_plan.covered_by_long_macros / cycle_plan.swaps if cycle_plan.swaps else 0.0
        print(
            "    "
            f"cycle #{index}: pivot={cycle_plan.pivot:,} swaps={cycle_plan.swaps:,} "
            f"macros={len(cycle_plan.macros):,} long={cycle_plan.long_macro_count:,} "
            f"coverage={cycle_coverage:.3%}"
        )

    return ok


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Cycle-arc compiler")
    parser.add_argument("files", nargs="+", help="Whole files to test")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V23 - CYCLE-ARC COMPILER                              ║")
    print("║  exact route -> directed active-ring arc macros             ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    ok = True
    for file_arg in args.files:
        ok = run_case(Path(file_arg).expanduser()) and ok
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
