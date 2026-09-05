#!/usr/bin/env python3
"""
RIDE V33 - Sender-side affine -> lane -> Fisher-Yates chain.

Model:
  - sender knows both scaffold source and exact target
  - hop 1 uses affine to make a global macro move
  - hop 2 uses a seeded lane orbit to improve meso structure
  - hop 3 uses a seeded Fisher-Yates orbit as the finisher
  - decoder would receive:
      {K/base, delta, (affine seed,k), (lane seed,k), (fy seed,k), hash}

This is the first concrete probe of the user's current architecture:
  K-coords get us into the right ingredient space,
  affine gets us close,
  lane tightens local geometry,
  FY does the last mile.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import time
from pathlib import Path
from typing import Any

import numpy as np

from ride_v13_canterbury_recipe_bench import (
    encode_svarint,
    encode_uvarint,
    leading_zero_bytes,
    materialize_bytes_from_decimal,
)
from ride_v16_whole_file_orbit_steps import PCG32
from ride_v19_pivot_cycle_orbit import materialise_source
from ride_v24_order_family_harness import (
    K_CANDIDATES,
    LANE_K_CANDIDATES,
    apply_perm_power,
    decompose_perm,
    fisher_yates_sigma,
    lane_rotate_state,
)
from ride_v29_affine_sigma_orbit import apply_affine_k, affine_sigma_order, make_affine_sigma
from ride_v31_sender_seed_search import (
    coarse_k_values,
    estimate_base_bytes,
    estimate_order_bytes,
    extract_chunk,
    fine_k_values,
)


def score_candidate(candidate: bytearray, target: bytearray) -> tuple[int, int]:
    mismatch = 0
    fixed = 0
    for left, right in zip(candidate, target):
        if left == right:
            fixed += 1
        else:
            mismatch += 1
    return mismatch, -fixed


def exact_hit_bytes(candidate: bytearray, raw_len: int, zero_prefix: int, raw_hash: str) -> bool:
    try:
        rebuilt = materialize_bytes_from_decimal(candidate, raw_len, zero_prefix)
    except (ValueError, OverflowError):
        return False
    return hashlib.sha256(rebuilt).hexdigest() == raw_hash


def compact_rows(rows: list[dict[str, Any]], limit: int) -> list[dict[str, Any]]:
    rows = sorted(rows, key=lambda row: (row["mismatch"], -row["fixed"]))
    unique: list[dict[str, Any]] = []
    seen: set[tuple[Any, ...]] = set()
    for row in rows:
        key = tuple((k, row[k]) for k in sorted(row) if k != "state")
        if key in seen:
            continue
        seen.add(key)
        clean = {k: v for k, v in row.items() if k != "state"}
        unique.append(clean)
        if len(unique) >= limit:
            break
    return unique


def lane_stride_palette(n: int) -> list[int]:
    raw = [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]
    palette = [value for value in raw if 1 < value < n]
    return palette if palette else [2]


def lane_stride_from_seed(seed: int, n: int) -> int:
    palette = lane_stride_palette(n)
    rng = PCG32(seed)
    return palette[rng.next_uniform(len(palette))]


def fy_k_values(cycles: list[list[int]]) -> list[int]:
    cycle_lengths = sorted((len(cycle) for cycle in cycles), reverse=True)[:6]
    extra = {
        value
        for length in cycle_lengths
        for value in (length // 4, length // 2, (3 * length) // 4, length - 1)
        if value > 0
    }
    return sorted(set(K_CANDIDATES) | extra)


def search_affine_candidates(
    source: bytearray,
    target: bytearray,
    raw_len: int,
    zero_prefix: int,
    raw_hash: str,
    coarse_seeds: int,
    coarse_k_samples: int,
    top_seed_count: int,
    fine_k_radius: int,
    max_k: int,
    shortlist: int,
    rng_seed: int,
) -> dict[str, Any]:
    source_np = np.array(source, dtype=np.uint8)
    target_np = np.array(target, dtype=np.uint8)
    n = len(target)
    rng = random.Random(rng_seed)

    coarse_rows: list[dict[str, Any]] = []
    full_rows: list[dict[str, Any]] = []
    best: dict[str, Any] | None = None

    t0 = time.perf_counter()
    for _ in range(coarse_seeds):
        seed = rng.randint(0, 2**32 - 1)
        a, b = make_affine_sigma(n, seed)
        order_cap = min(max_k, affine_sigma_order(a, b, n))
        best_local: dict[str, Any] | None = None
        for k in coarse_k_values(order_cap, coarse_k_samples):
            candidate_np = apply_affine_k(source_np, n, a, b, k)
            candidate = bytearray(candidate_np.tolist())
            mismatch, neg_fixed = score_candidate(candidate, target)
            row = {
                "family": "affine",
                "seed": seed,
                "a": a,
                "b": b,
                "k": k,
                "order_cap": order_cap,
                "mismatch": mismatch,
                "fixed": -neg_fixed,
                "exact": exact_hit_bytes(candidate, raw_len, zero_prefix, raw_hash),
                "state": candidate,
            }
            if best_local is None or (row["mismatch"], -row["fixed"]) < (best_local["mismatch"], -best_local["fixed"]):
                best_local = row
            if best is None or (row["mismatch"], -row["fixed"]) < (best["mismatch"], -best["fixed"]):
                best = row
        if best_local is not None:
            coarse_rows.append(best_local)

    coarse_rows.sort(key=lambda row: (row["mismatch"], -row["fixed"]))
    finalists = coarse_rows[:top_seed_count]

    for finalist in finalists:
        for k in fine_k_values(finalist["k"], finalist["order_cap"], fine_k_radius):
            candidate_np = apply_affine_k(source_np, n, finalist["a"], finalist["b"], k)
            candidate = bytearray(candidate_np.tolist())
            mismatch, neg_fixed = score_candidate(candidate, target)
            row = {
                "family": "affine",
                "seed": finalist["seed"],
                "a": finalist["a"],
                "b": finalist["b"],
                "k": k,
                "order_cap": finalist["order_cap"],
                "mismatch": mismatch,
                "fixed": -neg_fixed,
                "exact": exact_hit_bytes(candidate, raw_len, zero_prefix, raw_hash),
                "state": candidate,
            }
            full_rows.append(row)
            if best is None or (row["mismatch"], -row["fixed"]) < (best["mismatch"], -best["fixed"]):
                best = row

    elapsed = time.perf_counter() - t0
    ranked = sorted(full_rows or coarse_rows, key=lambda row: (row["mismatch"], -row["fixed"]))
    if not ranked:
        raise RuntimeError("affine search produced no candidates")
    return {
        "seconds": round(elapsed, 3),
        "best": {k: v for k, v in (best or ranked[0]).items() if k != "state"},
        "candidates": ranked[:shortlist],
        "top_coarse": compact_rows(coarse_rows, min(12, len(coarse_rows))),
    }


def search_lane_candidates(
    source: bytearray,
    target: bytearray,
    raw_len: int,
    zero_prefix: int,
    raw_hash: str,
    seeds: int,
    shortlist: int,
    rng_seed: int,
) -> dict[str, Any]:
    n = len(target)
    rng = random.Random(rng_seed)
    rows: list[dict[str, Any]] = []

    t0 = time.perf_counter()
    for _ in range(seeds):
        seed = rng.randint(0, 2**32 - 1)
        stride = lane_stride_from_seed(seed, n)
        for k in LANE_K_CANDIDATES:
            candidate = bytearray(lane_rotate_state(list(source), stride, k))
            mismatch, neg_fixed = score_candidate(candidate, target)
            rows.append(
                {
                    "family": "lane",
                    "seed": seed,
                    "stride": stride,
                    "k": k,
                    "mismatch": mismatch,
                    "fixed": -neg_fixed,
                    "exact": exact_hit_bytes(candidate, raw_len, zero_prefix, raw_hash),
                    "state": candidate,
                }
            )

    if not rows:
        raise RuntimeError("lane search produced no candidates")
    rows.sort(key=lambda row: (row["mismatch"], -row["fixed"]))
    elapsed = time.perf_counter() - t0
    return {
        "seconds": round(elapsed, 3),
        "best": {k: v for k, v in rows[0].items() if k != "state"},
        "candidates": rows[:shortlist],
        "top": compact_rows(rows, min(12, len(rows))),
    }


def search_fy_candidates(
    source: bytearray,
    target: bytearray,
    raw_len: int,
    zero_prefix: int,
    raw_hash: str,
    seeds: int,
    shortlist: int,
    rng_seed: int,
) -> dict[str, Any]:
    n = len(target)
    rng = random.Random(rng_seed)
    rows: list[dict[str, Any]] = []

    t0 = time.perf_counter()
    for _ in range(seeds):
        seed = rng.randint(0, 2**32 - 1)
        sigma = fisher_yates_sigma(n, seed)
        cycles = decompose_perm(sigma)
        for k in fy_k_values(cycles):
            if k == 0:
                continue
            candidate = bytearray(apply_perm_power(list(source), sigma, cycles, k))
            mismatch, neg_fixed = score_candidate(candidate, target)
            rows.append(
                {
                    "family": "fixed_fy",
                    "seed": seed,
                    "k": k,
                    "mismatch": mismatch,
                    "fixed": -neg_fixed,
                    "exact": exact_hit_bytes(candidate, raw_len, zero_prefix, raw_hash),
                    "state": candidate,
                }
            )

    if not rows:
        raise RuntimeError("fy search produced no candidates")
    rows.sort(key=lambda row: (row["mismatch"], -row["fixed"]))
    elapsed = time.perf_counter() - t0
    return {
        "seconds": round(elapsed, 3),
        "best": {k: v for k, v in rows[0].items() if k != "state"},
        "candidates": rows[:shortlist],
        "top": compact_rows(rows, min(12, len(rows))),
    }


def lane_order_bytes(seed: int, k: int) -> int:
    return 1 + len(encode_uvarint(seed)) + len(encode_svarint(k))


def fy_order_bytes(seed: int, k: int) -> int:
    return 1 + len(encode_uvarint(seed)) + len(encode_uvarint(k))


def search_chain(
    raw_chunk: bytes,
    affine_coarse_seeds: int,
    affine_coarse_k_samples: int,
    affine_top_seed_count: int,
    affine_fine_k_radius: int,
    affine_max_k: int,
    beam_affine: int,
    lane_seeds: int,
    beam_lane: int,
    fy_seeds: int,
    rng_seed: int,
) -> dict[str, Any]:
    t0 = time.perf_counter()
    source_digits, target_digits, params, delta, freq_l1 = materialise_source(raw_chunk)
    prep_seconds = time.perf_counter() - t0

    source = bytearray(source_digits)
    target = bytearray(target_digits)
    raw_hash = hashlib.sha256(raw_chunk).hexdigest()
    zero_prefix = leading_zero_bytes(raw_chunk)

    affine = search_affine_candidates(
        source=source,
        target=target,
        raw_len=len(raw_chunk),
        zero_prefix=zero_prefix,
        raw_hash=raw_hash,
        coarse_seeds=affine_coarse_seeds,
        coarse_k_samples=affine_coarse_k_samples,
        top_seed_count=affine_top_seed_count,
        fine_k_radius=affine_fine_k_radius,
        max_k=affine_max_k,
        shortlist=beam_affine,
        rng_seed=rng_seed,
    )

    best_chain: dict[str, Any] | None = None
    lane_reports: list[dict[str, Any]] = []
    fy_reports: list[dict[str, Any]] = []

    for affine_index, affine_row in enumerate(affine["candidates"][:beam_affine]):
        affine_state = affine_row["state"]
        lane = search_lane_candidates(
            source=affine_state,
            target=target,
            raw_len=len(raw_chunk),
            zero_prefix=zero_prefix,
            raw_hash=raw_hash,
            seeds=lane_seeds,
            shortlist=beam_lane,
            rng_seed=rng_seed ^ 0xA5A5A5A5 ^ int(affine_row["seed"]) ^ (affine_index << 8),
        )
        lane_reports.append(
            {
                "affine_index": affine_index,
                "from_affine": {k: v for k, v in affine_row.items() if k != "state"},
                "best": lane["best"],
                "seconds": lane["seconds"],
            }
        )

        for lane_index, lane_row in enumerate(lane["candidates"][:beam_lane]):
            lane_state = lane_row["state"]
            fy = search_fy_candidates(
                source=lane_state,
                target=target,
                raw_len=len(raw_chunk),
                zero_prefix=zero_prefix,
                raw_hash=raw_hash,
                seeds=fy_seeds,
                shortlist=1,
                rng_seed=rng_seed ^ 0x5A5A5A5A ^ int(affine_row["seed"]) ^ int(lane_row["seed"]) ^ (lane_index << 12),
            )
            fy_reports.append(
                {
                    "affine_index": affine_index,
                    "lane_index": lane_index,
                    "from_affine": {k: v for k, v in affine_row.items() if k != "state"},
                    "from_lane": {k: v for k, v in lane_row.items() if k != "state"},
                    "best": fy["best"],
                    "seconds": fy["seconds"],
                }
            )
            candidate = {
                "affine": {k: v for k, v in affine_row.items() if k != "state"},
                "lane": {k: v for k, v in lane_row.items() if k != "state"},
                "fy": fy["best"],
            }
            score = (fy["best"]["mismatch"], -fy["best"]["fixed"])
            if best_chain is None or score < (best_chain["fy"]["mismatch"], -best_chain["fy"]["fixed"]):
                best_chain = candidate
                if fy["best"]["exact"]:
                    break
        if best_chain is not None and best_chain["fy"]["exact"]:
            break

    if best_chain is None:
        raise RuntimeError("no chain candidates survived search")

    base_bytes = estimate_base_bytes(params, delta, raw_chunk)
    order_bytes = (
        estimate_order_bytes(best_chain["affine"]["seed"], best_chain["affine"]["k"], best_chain["affine"]["a"], best_chain["affine"]["b"])
        + lane_order_bytes(best_chain["lane"]["seed"], best_chain["lane"]["k"])
        + fy_order_bytes(best_chain["fy"]["seed"], best_chain["fy"]["k"])
    )
    total_bytes = base_bytes + order_bytes

    return {
        "raw_bytes": len(raw_chunk),
        "digits": len(target),
        "freq_l1": freq_l1,
        "prep_seconds": round(prep_seconds, 3),
        "exact": bool(best_chain["fy"]["exact"]),
        "affine_best": affine["best"],
        "best_chain": best_chain,
        "lane_reports": lane_reports[: min(8, len(lane_reports))],
        "fy_reports": fy_reports[: min(12, len(fy_reports))],
        "base_bytes": base_bytes,
        "order_bytes": order_bytes,
        "total_bytes": total_bytes,
        "ratio": round(len(raw_chunk) / total_bytes, 3) if total_bytes else 0.0,
        "target_hash": raw_hash,
    }


def run(
    path: Path,
    chunk_bytes: int,
    chunk_index: int,
    affine_coarse_seeds: int,
    affine_coarse_k_samples: int,
    affine_top_seed_count: int,
    affine_fine_k_radius: int,
    affine_max_k: int,
    beam_affine: int,
    lane_seeds: int,
    beam_lane: int,
    fy_seeds: int,
    rng_seed: int,
) -> dict[str, Any]:
    raw = path.read_bytes()
    chunk = extract_chunk(raw, chunk_bytes, chunk_index)
    result = search_chain(
        raw_chunk=chunk,
        affine_coarse_seeds=affine_coarse_seeds,
        affine_coarse_k_samples=affine_coarse_k_samples,
        affine_top_seed_count=affine_top_seed_count,
        affine_fine_k_radius=affine_fine_k_radius,
        affine_max_k=affine_max_k,
        beam_affine=beam_affine,
        lane_seeds=lane_seeds,
        beam_lane=beam_lane,
        fy_seeds=fy_seeds,
        rng_seed=rng_seed,
    )

    affine = result["best_chain"]["affine"]
    lane = result["best_chain"]["lane"]
    fy = result["best_chain"]["fy"]

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V33 — AFFINE -> LANE -> FY CHAIN                    ║")
    print("║  sender-side beam search, exact raw-byte hash gating      ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print(f"\nFile: {path}")
    print(f"Chunk bytes: {chunk_bytes:,}  chunk_index={chunk_index}")
    print(f"Chunk raw bytes: {len(chunk):,}")
    print(f"Digits: {result['digits']:,}  freq_L1={result['freq_l1']:,}  prep={result['prep_seconds']}s")
    print()
    print(
        f"Affine: seed={affine['seed']}  a={affine['a']}  b={affine['b']}  k={affine['k']}  "
        f"mismatch={affine['mismatch']:,}  fixed={affine['fixed']:,}"
    )
    print(
        f"Lane:   seed={lane['seed']}  stride={lane['stride']}  k={lane['k']}  "
        f"mismatch={lane['mismatch']:,}  fixed={lane['fixed']:,}"
    )
    print(
        f"FY:     seed={fy['seed']}  k={fy['k']}  mismatch={fy['mismatch']:,}  "
        f"fixed={fy['fixed']:,}  exact={'YES' if fy['exact'] else 'NO'}"
    )
    print(f"Packet estimate: base={result['base_bytes']}B  order={result['order_bytes']}B  total={result['total_bytes']}B")
    print(f"Ratio: {result['ratio']:.2f}x")
    return result


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="RIDE V33 — affine -> lane -> FY chain")
    parser.add_argument("file", help="File to probe")
    parser.add_argument("--chunk-bytes", type=int, default=10_240)
    parser.add_argument("--chunk-index", type=int, default=0)
    parser.add_argument("--affine-coarse-seeds", type=int, default=96)
    parser.add_argument("--affine-coarse-k-samples", type=int, default=24)
    parser.add_argument("--affine-top-seeds", type=int, default=8)
    parser.add_argument("--affine-fine-k-radius", type=int, default=48)
    parser.add_argument("--affine-max-k", type=int, default=2048)
    parser.add_argument("--beam-affine", type=int, default=4)
    parser.add_argument("--lane-seeds", type=int, default=48)
    parser.add_argument("--beam-lane", type=int, default=3)
    parser.add_argument("--fy-seeds", type=int, default=24)
    parser.add_argument("--rng-seed", type=int, default=42)
    parser.add_argument("--json-out")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    result = run(
        Path(args.file).expanduser(),
        chunk_bytes=args.chunk_bytes,
        chunk_index=args.chunk_index,
        affine_coarse_seeds=args.affine_coarse_seeds,
        affine_coarse_k_samples=args.affine_coarse_k_samples,
        affine_top_seed_count=args.affine_top_seeds,
        affine_fine_k_radius=args.affine_fine_k_radius,
        affine_max_k=args.affine_max_k,
        beam_affine=args.beam_affine,
        lane_seeds=args.lane_seeds,
        beam_lane=args.beam_lane,
        fy_seeds=args.fy_seeds,
        rng_seed=args.rng_seed,
    )
    if args.json_out:
        json_path = Path(args.json_out).expanduser()
        json_path.write_text(json.dumps(result, indent=2))
        print(f"\nJSON report written to {json_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
