#!/usr/bin/env python3
"""
RIDE V21 - Block-move macro-to-micro planner.

Compared with V20:
  - macro op is now cut-and-insert block move, not equal-length block swap
  - this is a stronger primitive for long-cycle permutations

Macro op:
  M(src_start, dst_start, length)
  Meaning:
    cut path[src_start:src_start+length] and insert it at dst_start

Micro op:
  S(a, b)

This checks whether real files contain harvestable contiguous target runs once
we allow insertion instead of requiring a partner block.
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
    deterministic_frequency_patch,
    encode_uvarint,
    permutation_cycle_mile,
    str_to_digits,
)
from ride_v2_kpog_encoder import build_permutation


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


def encode_op_bytes(op: tuple) -> int:
    tag = op[0]
    if tag == "M":
        _, src, dst, length = op
        return 1 + len(encode_uvarint(src)) + len(encode_uvarint(dst)) + len(encode_uvarint(length))
    if tag == "S":
        _, a, b = op
        return 1 + len(encode_uvarint(a)) + len(encode_uvarint(b))
    raise ValueError(f"unknown op tag: {tag}")


def swap_positions(path: list[int], id_to_index: list[int], a: int, b: int) -> None:
    x = path[a]
    y = path[b]
    path[a], path[b] = y, x
    id_to_index[x] = b
    id_to_index[y] = a


def move_block(path: list[int], id_to_index: list[int], src: int, dst: int, length: int) -> None:
    if length <= 0 or src == dst:
        return
    block = path[src:src + length]
    del path[src:src + length]
    if src < dst:
        dst -= length
    path[dst:dst] = block
    for idx, token in enumerate(path):
        id_to_index[token] = idx


def contiguous_target_run(path: list[int], target_order: list[int], p: int, q: int, max_probe: int | None) -> int:
    n = len(path)
    max_len = min(n - p, n - q)
    if max_probe is not None:
        max_len = min(max_len, max_probe)
    length = 0
    while length < max_len and path[q + length] == target_order[p + length]:
        length += 1
    return length


def choose_focus(path: list[int], target_order: list[int], id_to_index: list[int], cursor: int, window: int) -> tuple[int, int] | None:
    n = len(path)
    end = min(n, cursor + window)
    best: tuple[int, int, int] | None = None
    for p in range(cursor, end):
        if path[p] == target_order[p]:
            continue
        q = id_to_index[target_order[p]]
        displacement = abs(q - p)
        candidate = (displacement, -p, q)
        if best is None or candidate > best:
            best = candidate
    if best is None:
        return None
    displacement, neg_p, q = best
    return -neg_p, q


def block_move_plan(
    target_order: list[int],
    *,
    focus_window: int = 128,
    min_block: int = 8,
    max_probe: int = 4096,
) -> dict:
    n = len(target_order)
    path = list(range(n))
    id_to_index = list(range(n))
    cursor = 0
    ops: list[tuple] = []
    move_ops = 0
    single_ops = 0
    total_move_tokens = 0
    max_move_len = 0

    while cursor < n:
        while cursor < n and path[cursor] == target_order[cursor]:
            cursor += 1
        if cursor >= n:
            break

        focus = choose_focus(path, target_order, id_to_index, cursor, focus_window)
        if focus is None:
            q = id_to_index[target_order[cursor]]
            swap_positions(path, id_to_index, cursor, q)
            ops.append(("S", cursor, q))
            single_ops += 1
            continue

        p, q = focus
        run_len = contiguous_target_run(path, target_order, p, q, max_probe=max_probe)
        if run_len >= min_block:
            move_block(path, id_to_index, q, p, run_len)
            ops.append(("M", q, p, run_len))
            move_ops += 1
            total_move_tokens += run_len
            max_move_len = max(max_move_len, run_len)
        else:
            q = id_to_index[target_order[p]]
            swap_positions(path, id_to_index, p, q)
            ops.append(("S", p, q))
            single_ops += 1

    total_bytes = sum(encode_op_bytes(op) for op in ops)
    return {
        "ops": ops,
        "move_ops": move_ops,
        "single_ops": single_ops,
        "total_bytes": total_bytes,
        "total_move_tokens": total_move_tokens,
        "max_move_len": max_move_len,
        "path": path,
    }


def run_case(path: Path, focus_window: int, min_block: int, max_probe: int) -> bool:
    raw = path.read_bytes()
    print(f"\n{'=' * 72}")
    print(f"  Block-move RSN case: {path.name}")
    print(f"{'=' * 72}")
    print(f"  Raw bytes: {len(raw):,}")

    t0 = time.perf_counter()
    source_digits, target_digits, params, l1 = materialise_source_and_target(raw)
    prep_time = time.perf_counter() - t0

    t1 = time.perf_counter()
    perm = build_permutation(target_digits, source_digits)
    mile, cycles = permutation_cycle_mile(perm)
    plan = block_move_plan(
        perm,
        focus_window=focus_window,
        min_block=min_block,
        max_probe=max_probe,
    )
    plan_time = time.perf_counter() - t1

    ok = plan["path"] == perm

    print(f"  K params: v0={params[0]:,} a={params[1]:,} b={params[2]:,} v9={params[3]:,}")
    print(f"  Frequency delta L1: {l1:,}")
    print(f"  Prep time: {prep_time:.2f}s")
    print(f"  Mile (min transpositions): {mile:,}")
    print(f"  Total cycles: {cycles:,}")
    print(f"  Move ops: {plan['move_ops']:,}")
    print(f"  Single ops: {plan['single_ops']:,}")
    print(f"  Total ops: {len(plan['ops']):,}")
    print(f"  Op bytes (raw uvarint est): {plan['total_bytes']:,}B")
    print(f"  Largest move: {plan['max_move_len']:,}")
    print(f"  Total moved tokens: {plan['total_move_tokens']:,}")
    print(f"  Plan time: {plan_time:.2f}s")
    print(f"  Exact reconstruction: {'YES' if ok else 'NO'}")
    return ok


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Block-move RSN planner")
    parser.add_argument("file", help="Whole file to test")
    parser.add_argument("--focus-window", type=int, default=128)
    parser.add_argument("--min-block", type=int, default=8)
    parser.add_argument("--max-probe", type=int, default=4096)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V21 - BLOCK MOVE RSN                                  ║")
    print("║  cut-and-insert blocks, single swaps to finish              ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    ok = run_case(
        Path(args.file).expanduser(),
        focus_window=args.focus_window,
        min_block=args.min_block,
        max_probe=args.max_probe,
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
