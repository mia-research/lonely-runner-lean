#!/usr/bin/env python3
"""
RIDE V32 - Two-hop sender-side seed chain.

Model:
  - sender knows both source and target
  - hop 1 finds a large affine jump toward the target
  - hop 2 searches again from the residual state for fine correction
  - decoder would receive only:
      {K/base, delta, (family, seed_1, a_1, b_1, k_1), (family, seed_2, a_2, b_2, k_2), hash}

This is the concrete "macro jump then fine increment" probe.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path
from typing import Any

import numpy as np

from ride_v19_pivot_cycle_orbit import materialise_source
from ride_v29_affine_sigma_orbit import apply_affine_k
from ride_v31_sender_seed_search import (
    coarse_k_values,
    estimate_base_bytes,
    estimate_order_bytes,
    extract_chunk,
    fine_k_values,
    make_affine_sigma,
    affine_sigma_order,
)


def score_candidate(candidate: np.ndarray, target: np.ndarray) -> tuple[int, int]:
    mismatch = int(np.sum(candidate != target))
    fixed = int(np.sum(candidate == target))
    return mismatch, -fixed


def exact_hit(candidate: np.ndarray, target_hash: str) -> bool:
    return hashlib.sha256(candidate.tobytes()).hexdigest() == target_hash


def compact_hop_result(hop: dict[str, Any]) -> dict[str, Any]:
    return {
        "best": hop["best"],
        "coarse_seconds": hop["coarse_seconds"],
        "fine_seconds": hop["fine_seconds"],
        "top_coarse": hop["top_coarse"],
        "top_fine": hop["top_fine"],
    }


def shortlist_rows(hop: dict[str, Any], limit: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = [hop["best"], *hop["top_fine"], *hop["top_coarse"]]
    seen: set[tuple[int, int, int, int]] = set()
    unique: list[dict[str, Any]] = []
    for row in rows:
        key = (int(row["seed"]), int(row["a"]), int(row["b"]), int(row["k"]))
        if key in seen:
            continue
        seen.add(key)
        unique.append(row)
        if len(unique) >= limit:
            break
    return unique


def search_affine_once(
    source: np.ndarray,
    target: np.ndarray,
    coarse_seeds: int,
    coarse_k_samples: int,
    top_seed_count: int,
    fine_k_radius: int,
    max_k: int,
    rng_seed: int,
) -> dict[str, Any]:
    n = len(target)
    target_hash = hashlib.sha256(target.tobytes()).hexdigest()

    import random

    rng = random.Random(rng_seed)
    coarse_rows: list[dict[str, Any]] = []
    best: dict[str, Any] | None = None

    t1 = time.perf_counter()
    for _ in range(coarse_seeds):
        seed = rng.randint(0, 2**32 - 1)
        a, b = make_affine_sigma(n, seed)
        order_cap = min(max_k, affine_sigma_order(a, b, n))
        best_local: dict[str, Any] | None = None

        for k in coarse_k_values(order_cap, coarse_k_samples):
            candidate = apply_affine_k(source, n, a, b, k)
            mm, neg_fixed = score_candidate(candidate, target)
            row = {
                "seed": seed,
                "a": a,
                "b": b,
                "k": k,
                "order_cap": order_cap,
                "mismatch": mm,
                "fixed": -neg_fixed,
                "exact": exact_hit(candidate, target_hash),
            }
            if best_local is None or (row["mismatch"], -row["fixed"]) < (best_local["mismatch"], -best_local["fixed"]):
                best_local = row
            if best is None or (row["mismatch"], -row["fixed"]) < (best["mismatch"], -best["fixed"]):
                best = row
                if row["exact"]:
                    break
        if best_local is not None:
            coarse_rows.append(best_local)
        if best is not None and best["exact"]:
            break

    coarse_s = time.perf_counter() - t1
    coarse_rows.sort(key=lambda row: (row["mismatch"], -row["fixed"]))
    finalists = coarse_rows[:top_seed_count]

    fine_rows: list[dict[str, Any]] = []
    t2 = time.perf_counter()
    if best is None or not best["exact"]:
        for finalist in finalists:
            seed = finalist["seed"]
            a = finalist["a"]
            b = finalist["b"]
            order_cap = finalist["order_cap"]
            for k in fine_k_values(finalist["k"], order_cap, fine_k_radius):
                candidate = apply_affine_k(source, n, a, b, k)
                mm, neg_fixed = score_candidate(candidate, target)
                row = {
                    "seed": seed,
                    "a": a,
                    "b": b,
                    "k": k,
                    "order_cap": order_cap,
                    "mismatch": mm,
                    "fixed": -neg_fixed,
                    "exact": exact_hit(candidate, target_hash),
                }
                fine_rows.append(row)
                if best is None or (row["mismatch"], -row["fixed"]) < (best["mismatch"], -best["fixed"]):
                    best = row
                    if row["exact"]:
                        break
            if best is not None and best["exact"]:
                break
    fine_s = time.perf_counter() - t2

    if best is None:
        raise RuntimeError("search produced no affine candidates")

    best_state = apply_affine_k(source, n, best["a"], best["b"], best["k"])
    return {
        "best": best,
        "state": best_state,
        "coarse_seconds": round(coarse_s, 3),
        "fine_seconds": round(fine_s, 3),
        "top_coarse": finalists,
        "top_fine": sorted(fine_rows, key=lambda row: (row["mismatch"], -row["fixed"]))[: min(12, len(fine_rows))],
    }


def search_affine_chain(
    raw_chunk: bytes,
    coarse_seeds_1: int,
    coarse_seeds_2: int,
    coarse_k_samples: int,
    top_seed_count: int,
    hop1_branch_count: int,
    fine_k_radius_1: int,
    fine_k_radius_2: int,
    max_k_1: int,
    max_k_2: int,
    rng_seed: int,
) -> dict[str, Any]:
    t0 = time.perf_counter()
    source_digits, target_digits, params, delta, freq_l1 = materialise_source(raw_chunk)
    prep_s = time.perf_counter() - t0

    source = np.array(source_digits, dtype=np.uint8)
    target = np.array(target_digits, dtype=np.uint8)
    n = len(target_digits)

    hop1 = search_affine_once(
        source=source,
        target=target,
        coarse_seeds=coarse_seeds_1,
        coarse_k_samples=coarse_k_samples,
        top_seed_count=top_seed_count,
        fine_k_radius=fine_k_radius_1,
        max_k=max_k_1,
        rng_seed=rng_seed,
    )

    branch_rows = shortlist_rows(hop1, hop1_branch_count)
    best_chain: dict[str, Any] | None = None

    for branch_index, row in enumerate(branch_rows):
        branch_state = apply_affine_k(source, n, row["a"], row["b"], row["k"])
        hop2 = search_affine_once(
            source=branch_state,
            target=target,
            coarse_seeds=coarse_seeds_2,
            coarse_k_samples=coarse_k_samples,
            top_seed_count=top_seed_count,
            fine_k_radius=fine_k_radius_2,
            max_k=max_k_2,
            rng_seed=(rng_seed ^ 0x9E3779B97F4A7C15 ^ (branch_index << 8) ^ int(row["seed"])),
        )
        candidate_chain = {
            "branch_index": branch_index,
            "hop1_ranked_choice": row,
            "hop2": hop2,
        }
        score = (hop2["best"]["mismatch"], -hop2["best"]["fixed"])
        if best_chain is None or score < (
            best_chain["hop2"]["best"]["mismatch"],
            -best_chain["hop2"]["best"]["fixed"],
        ):
            best_chain = candidate_chain
            if hop2["best"]["exact"]:
                break

    if best_chain is None:
        raise RuntimeError("two-hop search produced no chain candidates")

    best1 = best_chain["hop1_ranked_choice"]
    hop2 = best_chain["hop2"]
    best2 = hop2["best"]
    exact = bool(best2["exact"])

    base_bytes = estimate_base_bytes(params, delta, raw_chunk)
    order_bytes = (
        estimate_order_bytes(best1["seed"], best1["k"], best1["a"], best1["b"])
        + estimate_order_bytes(best2["seed"], best2["k"], best2["a"], best2["b"])
    )
    total_bytes = base_bytes + order_bytes

    return {
        "raw_bytes": len(raw_chunk),
        "digits": n,
        "freq_l1": freq_l1,
        "prep_seconds": round(prep_s, 3),
        "exact": exact,
        "hop1": compact_hop_result(hop1),
        "hop2": compact_hop_result(hop2),
        "selected_hop1": best1,
        "hop1_branch_count": len(branch_rows),
        "selected_branch_index": best_chain["branch_index"],
        "base_bytes": base_bytes,
        "order_bytes": order_bytes,
        "total_bytes": total_bytes,
        "ratio": round(len(raw_chunk) / total_bytes, 3) if total_bytes else 0.0,
        "target_hash": hashlib.sha256(raw_chunk).hexdigest(),
    }


def run(
    path: Path,
    chunk_bytes: int,
    chunk_index: int,
    coarse_seeds_1: int,
    coarse_seeds_2: int,
    coarse_k_samples: int,
    top_seed_count: int,
    hop1_branch_count: int,
    fine_k_radius_1: int,
    fine_k_radius_2: int,
    max_k_1: int,
    max_k_2: int,
    rng_seed: int,
) -> dict[str, Any]:
    raw = path.read_bytes()
    chunk = extract_chunk(raw, chunk_bytes, chunk_index)
    result = search_affine_chain(
        raw_chunk=chunk,
        coarse_seeds_1=coarse_seeds_1,
        coarse_seeds_2=coarse_seeds_2,
        coarse_k_samples=coarse_k_samples,
        top_seed_count=top_seed_count,
        hop1_branch_count=hop1_branch_count,
        fine_k_radius_1=fine_k_radius_1,
        fine_k_radius_2=fine_k_radius_2,
        max_k_1=max_k_1,
        max_k_2=max_k_2,
        rng_seed=rng_seed,
    )

    best1 = result["selected_hop1"]
    best2 = result["hop2"]["best"]

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V32 — TWO-HOP SENDER SEED CHAIN                      ║")
    print("║  macro affine jump + fine affine correction                ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print(f"\nFile: {path}")
    print(f"Chunk bytes: {chunk_bytes:,}  chunk_index={chunk_index}")
    print(f"Chunk raw bytes: {len(chunk):,}")
    print(f"Digits: {result['digits']:,}  freq_L1={result['freq_l1']:,}  prep={result['prep_seconds']}s")
    print()
    print(
        f"Selected hop1 branch: {result['selected_branch_index'] + 1}/{result['hop1_branch_count']}  "
        f"seed={best1['seed']}  a={best1['a']}  b={best1['b']}  k={best1['k']}"
    )
    print(
        f"Hop1: mismatch={best1['mismatch']:,}  fixed={best1['fixed']:,}  "
        f"time={result['hop1']['coarse_seconds'] + result['hop1']['fine_seconds']:.3f}s"
    )
    print(
        f"Hop2: seed={best2['seed']}  a={best2['a']}  b={best2['b']}  k={best2['k']}  "
        f"mismatch={best2['mismatch']:,}  fixed={best2['fixed']:,}  "
        f"time={result['hop2']['coarse_seconds'] + result['hop2']['fine_seconds']:.3f}s"
    )
    print(f"Exact: {'YES' if result['exact'] else 'NO'}")
    print(f"Packet estimate: base={result['base_bytes']}B  order={result['order_bytes']}B  total={result['total_bytes']}B")
    print(f"Ratio: {result['ratio']:.2f}x")
    return result


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="RIDE V32 — two-hop sender-side seed chain")
    parser.add_argument("file", help="File to probe")
    parser.add_argument("--chunk-bytes", type=int, default=10_240)
    parser.add_argument("--chunk-index", type=int, default=0)
    parser.add_argument("--coarse-seeds-1", type=int, default=96)
    parser.add_argument("--coarse-seeds-2", type=int, default=64)
    parser.add_argument("--coarse-k-samples", type=int, default=24)
    parser.add_argument("--top-seeds", type=int, default=8)
    parser.add_argument("--hop1-branches", type=int, default=4)
    parser.add_argument("--fine-k-radius-1", type=int, default=48)
    parser.add_argument("--fine-k-radius-2", type=int, default=64)
    parser.add_argument("--max-k-1", type=int, default=2048)
    parser.add_argument("--max-k-2", type=int, default=1024)
    parser.add_argument("--rng-seed", type=int, default=42)
    parser.add_argument("--json-out")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    result = run(
        Path(args.file).expanduser(),
        chunk_bytes=args.chunk_bytes,
        chunk_index=args.chunk_index,
        coarse_seeds_1=args.coarse_seeds_1,
        coarse_seeds_2=args.coarse_seeds_2,
        coarse_k_samples=args.coarse_k_samples,
        top_seed_count=args.top_seeds,
        hop1_branch_count=args.hop1_branches,
        fine_k_radius_1=args.fine_k_radius_1,
        fine_k_radius_2=args.fine_k_radius_2,
        max_k_1=args.max_k_1,
        max_k_2=args.max_k_2,
        rng_seed=args.rng_seed,
    )
    if args.json_out:
        json_path = Path(args.json_out).expanduser()
        json_path.write_text(json.dumps(result, indent=2))
        print(f"\nJSON report written to {json_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
