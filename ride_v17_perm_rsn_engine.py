#!/usr/bin/env python3
"""
RIDE V17 - Permutation-space RSN engine.

This is not a plug-and-play reuse of the TSP solver. It translates the RSN
mechanics into permutation space:

  - cities           -> source-index tokens
  - city coordinates -> desired target positions on a 1D line
  - current path     -> current ordering of source tokens
  - stress           -> detour in target-position geometry
  - phase B move     -> best local segment reversal (2-opt analogue)

Goal:
  understand whether RSN-style focus-set + local reversals reduces the whole
  file ordering problem to a small number of deterministic macro-steps.

This is encoder-side geometry for now. It does not yet solve the decoder-shared
orbit problem, but it gives us the right altered engine to study.
"""

from __future__ import annotations

import argparse
import hashlib
import math
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


def build_target_geometry(target_digits: bytearray, source_digits: bytearray) -> tuple[list[int], list[int]]:
    """
    Return:
      target_order[source_pos] at each target position
      target_pos[source_pos]    inverse mapping
    """
    perm = build_perm_target_to_source(target_digits, source_digits)
    target_order = list(perm)
    n = len(target_order)
    target_pos = [0] * n
    for pos, source_idx in enumerate(target_order):
        target_pos[source_idx] = pos
    return target_order, target_pos


def path_cost(path: list[int], target_pos: list[int]) -> int:
    """
    Open-chain cost with anchored virtual endpoints:
      start at -1, end at N
    """
    if not path:
        return 0
    n = len(path)
    cost = target_pos[path[0]] + 1
    for i in range(n - 1):
        cost += abs(target_pos[path[i + 1]] - target_pos[path[i]])
    cost += n - target_pos[path[-1]]
    return cost


def triple_stress(prev_city: int, city: int, next_city: int, target_pos: list[int]) -> float:
    a = target_pos[prev_city]
    b = target_pos[city]
    c = target_pos[next_city]
    d_ab = abs(a - b)
    d_bc = abs(b - c)
    d_ac = abs(a - c)
    return ((d_ab + d_bc) / (d_ac + 1e-9)) * (d_ab + d_bc)


def phase_a_focus(path: list[int], target_pos: list[int], focus_size: int) -> list[tuple[float, int]]:
    n = len(path)
    scores: list[tuple[float, int]] = []
    if n < 3:
        return scores
    for i in range(1, n - 1):
        score = triple_stress(path[i - 1], path[i], path[i + 1], target_pos)
        if score > 0:
            scores.append((score, i))
    scores.sort(key=lambda item: item[0], reverse=True)
    return scores[:focus_size]


def reversal_delta(path: list[int], target_pos: list[int], left: int, right: int) -> int:
    """
    Improvement in anchored open-chain cost from reversing [left, right].
    Positive means better.
    """
    n = len(path)

    def left_coord(index: int) -> int:
        return -1 if index < 0 else target_pos[path[index]]

    def right_coord(index: int) -> int:
        return n if index >= n else target_pos[path[index]]

    old = abs(right_coord(left) - left_coord(left - 1))
    old += abs(right_coord(right + 1) - left_coord(right))

    new = abs(right_coord(right) - left_coord(left - 1))
    new += abs(right_coord(right + 1) - left_coord(left))
    return old - new


def reverse_segment(path: list[int], id_to_index: list[int], left: int, right: int) -> None:
    segment = path[left:right + 1]
    segment.reverse()
    path[left:right + 1] = segment
    for offset, city in enumerate(segment):
        id_to_index[city] = left + offset


def rsn_permutation_refinement(
    target_order: list[int],
    target_pos: list[int],
    *,
    max_iterations: int = 200,
    focus_size: int = 1024,
    partner_depth: int = 8,
    max_no_improve: int = 8,
) -> dict:
    """
    Deterministic RSN-style refinement in permutation space.

    Partners are chosen from the cities that should be adjacent to the focus city
    in target order. The move is the best improving segment reversal.
    """
    n = len(target_order)
    path = list(range(n))
    id_to_index = list(range(n))
    target_inverse = target_order

    current_cost = path_cost(path, target_pos)
    best_cost = current_cost
    improvements = 0
    no_improve_iters = 0
    history: list[dict] = []

    for iteration in range(1, max_iterations + 1):
        if path == target_order:
            return {
                "hit": True,
                "iterations": iteration - 1,
                "improvements": improvements,
                "cost": current_cost,
                "history": history,
                "path": path,
            }

        focus = phase_a_focus(path, target_pos, focus_size)
        if not focus:
            break

        best_move: tuple[int, int, int, float, int] | None = None
        # (delta, left, right, stress, focus_index)
        for stress, focus_index in focus:
            city = path[focus_index]
            t = target_pos[city]
            for offset in range(1, partner_depth + 1):
                for neighbor_rank in (t - offset, t + offset):
                    if not (0 <= neighbor_rank < n):
                        continue
                    partner_city = target_inverse[neighbor_rank]
                    partner_index = id_to_index[partner_city]
                    if partner_index == focus_index:
                        continue
                    left = min(focus_index, partner_index)
                    right = max(focus_index, partner_index)
                    if right - left < 1:
                        continue
                    delta = reversal_delta(path, target_pos, left, right)
                    if delta <= 0:
                        continue
                    candidate = (delta, left, right, stress, focus_index)
                    if best_move is None:
                        best_move = candidate
                        continue
                    # Deterministic tie-break: bigger improvement, then shorter segment,
                    # then higher stress, then earlier left boundary.
                    prev = best_move
                    if delta > prev[0]:
                        best_move = candidate
                    elif delta == prev[0]:
                        seg_len = right - left
                        prev_len = prev[2] - prev[1]
                        if seg_len < prev_len:
                            best_move = candidate
                        elif seg_len == prev_len:
                            if stress > prev[3]:
                                best_move = candidate
                            elif stress == prev[3] and left < prev[1]:
                                best_move = candidate

        if best_move is None:
            no_improve_iters += 1
            history.append(
                {
                    "iteration": iteration,
                    "focus": len(focus),
                    "improved": False,
                    "cost": current_cost,
                }
            )
            if no_improve_iters >= max_no_improve:
                break
            continue

        no_improve_iters = 0
        delta, left, right, stress, focus_index = best_move
        reverse_segment(path, id_to_index, left, right)
        current_cost -= delta
        best_cost = min(best_cost, current_cost)
        improvements += 1
        history.append(
            {
                "iteration": iteration,
                "focus": len(focus),
                "improved": True,
                "delta": delta,
                "left": left,
                "right": right,
                "stress": stress,
                "cost": current_cost,
            }
        )

    return {
        "hit": path == target_order,
        "iterations": len(history),
        "improvements": improvements,
        "cost": current_cost,
        "history": history,
        "path": path,
    }


def materialise_source_and_target(raw: bytes) -> tuple[bytearray, bytearray, tuple[int, int, int, int], int]:
    decimal = binary_to_decimal_lossless(raw)
    target_counts = digit_counts(decimal)
    target_digits = bytearray(str_to_digits(decimal))

    v0, a, b, v9, l1 = nearest_thermo_params(target_counts)
    thermo_counts = thermo_counts_from_params(v0, a, b, v9)
    seed = construct_pivot_seed(thermo_counts)
    k_constant, _steps, status = iterate_to_fixed(seed, max_iter=30)
    if k_constant is None:
        raise ValueError(f"K materialisation failed with status={status}")
    k_digits = bytearray(str_to_digits(k_constant))
    patched_source, _delta, _edits = deterministic_frequency_patch(k_digits, target_counts)
    return patched_source, target_digits, (v0, a, b, v9), l1


def run_case(path: Path, max_iterations: int, focus_size: int, partner_depth: int) -> bool:
    raw = path.read_bytes()
    print(f"\n{'=' * 72}")
    print(f"  Permutation-space RSN case: {path.name}")
    print(f"{'=' * 72}")
    print(f"  Raw bytes: {len(raw):,}")

    t0 = time.perf_counter()
    source_digits, target_digits, params, l1 = materialise_source_and_target(raw)
    prep_time = time.perf_counter() - t0

    t1 = time.perf_counter()
    target_order, target_pos = build_target_geometry(target_digits, source_digits)
    perm = build_perm_target_to_source(target_digits, source_digits)
    mile, cycles = permutation_cycle_mile(perm)
    initial_cost = path_cost(list(range(len(target_order))), target_pos)
    setup_time = time.perf_counter() - t1

    t2 = time.perf_counter()
    result = rsn_permutation_refinement(
        target_order,
        target_pos,
        max_iterations=max_iterations,
        focus_size=focus_size,
        partner_depth=partner_depth,
    )
    rsn_time = time.perf_counter() - t2

    final_path = result["path"]
    final_hash = hashlib.sha256(bytes(target_digits)).hexdigest()
    hit = bool(result["hit"])
    exact = final_path == target_order

    print(f"  K params: v0={params[0]:,} a={params[1]:,} b={params[2]:,} v9={params[3]:,}")
    print(f"  Frequency delta L1: {l1:,}")
    print(f"  Prep time: {prep_time:.2f}s")
    print(f"  Target geometry setup: {setup_time:.2f}s")
    print(f"  Mile (min transpositions): {mile:,}  cycles: {cycles:,}")
    print(f"  Initial RSN cost: {initial_cost:,}")
    print(f"  RSN iterations: {result['iterations']:,}")
    print(f"  RSN improving moves: {result['improvements']:,}")
    print(f"  Final RSN cost: {result['cost']:,}")
    print(f"  RSN time: {rsn_time:.2f}s")
    print(f"  Exact target hit: {'YES' if exact else 'NO'}")
    if result["history"]:
        first = result["history"][0]
        last = result["history"][-1]
        print(f"  First move delta: {first.get('delta', 0):,}  Last cost: {last.get('cost', result['cost']):,}")
    print(f"  Target hash: {final_hash[:16]}...")
    return hit


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Permutation-space RSN engine probe")
    parser.add_argument("file", help="Whole file to test")
    parser.add_argument("--max-iterations", type=int, default=200)
    parser.add_argument("--focus-size", type=int, default=1024)
    parser.add_argument("--partner-depth", type=int, default=8)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V17 - PERMUTATION-SPACE RSN ENGINE                    ║")
    print("║  stress + focus set + segment reversals                     ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    ok = run_case(
        Path(args.file).expanduser(),
        max_iterations=args.max_iterations,
        focus_size=args.focus_size,
        partner_depth=args.partner_depth,
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
