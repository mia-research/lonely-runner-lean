#!/usr/bin/env python3
"""
RIDE V31 - Sender-side seed+k search engine for a target chunk.

This is the architectural pivot:
  - the sender knows both source and target
  - the sender searches for a decoder-replayable seed that induces a useful orbit
  - the packet carries only {family_id, seed, k, hash} on the order side

Current implementation:
  - affine family only (global reach, exact jump-ahead)
  - two-step search:
      1. coarse scan over many seeds and sparse k samples
      2. fine search around the best coarse neighbourhoods

This is not a finished codec. It is a sender-side feasibility probe for 10KB
targets using the real K-materialisation front end.
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

from ride_v13_canterbury_recipe_bench import encode_svarint, encode_uvarint, leading_zero_bytes
from ride_v19_pivot_cycle_orbit import materialise_source
from ride_v29_affine_sigma_orbit import apply_affine_k, affine_sigma_order, make_affine_sigma


def estimate_base_bytes(params: tuple[int, int, int, int], delta: list[int], raw: bytes) -> int:
    k_bytes = sum(len(encode_uvarint(value)) for value in params)
    delta_bytes = sum(len(encode_svarint(value)) for value in delta)
    meta_bytes = len(encode_uvarint(len(raw))) + len(encode_uvarint(leading_zero_bytes(raw)))
    hash_bytes = 32
    return k_bytes + delta_bytes + meta_bytes + hash_bytes


def estimate_order_bytes(seed: int, k: int, a: int, b: int) -> int:
    family_bytes = 1
    return (
        family_bytes
        + len(encode_uvarint(seed))
        + len(encode_uvarint(a))
        + len(encode_uvarint(b))
        + len(encode_uvarint(k))
    )


def mismatch(candidate: np.ndarray, target: np.ndarray) -> int:
    return int(np.sum(candidate != target))


def exact_hit(candidate: np.ndarray, target_hash: str) -> bool:
    return hashlib.sha256(candidate.tobytes()).hexdigest() == target_hash


def score_candidate(candidate: np.ndarray, target: np.ndarray) -> tuple[int, int]:
    mm = mismatch(candidate, target)
    fixed = int(np.sum(candidate == target))
    return mm, -fixed


def coarse_k_values(cap: int, samples: int) -> list[int]:
    if cap <= 1:
        return [1]
    if samples <= 1:
        return [1, cap] if cap > 1 else [1]
    ks = {1, cap}
    for idx in range(samples):
        frac = idx / max(1, samples - 1)
        k = 1 + int(round(frac * (cap - 1)))
        ks.add(max(1, min(cap, k)))
    return sorted(ks)


def fine_k_values(center: int, cap: int, radius: int) -> list[int]:
    lower = max(1, center - radius)
    upper = min(cap, center + radius)
    return list(range(lower, upper + 1))


def extract_chunk(raw: bytes, chunk_bytes: int, chunk_index: int) -> bytes:
    start = chunk_index * chunk_bytes
    end = start + chunk_bytes
    chunk = raw[start:end]
    if not chunk:
        raise ValueError(f"chunk_index={chunk_index} out of range for chunk_bytes={chunk_bytes}")
    return chunk


def search_affine_seed_engine(
    raw_chunk: bytes,
    coarse_seeds: int,
    coarse_k_samples: int,
    top_seed_count: int,
    fine_k_radius: int,
    max_k: int,
    rng_seed: int,
) -> dict[str, Any]:
    t0 = time.perf_counter()
    source_digits, target_digits, params, delta, freq_l1 = materialise_source(raw_chunk)
    prep_s = time.perf_counter() - t0

    source = np.array(source_digits, dtype=np.uint8)
    target = np.array(target_digits, dtype=np.uint8)
    n = len(target_digits)
    target_hash = hashlib.sha256(target.tobytes()).hexdigest()

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
        raise RuntimeError("seed search produced no candidates")

    base_bytes = estimate_base_bytes(params, delta, raw_chunk)
    order_bytes = estimate_order_bytes(best["seed"], best["k"], best["a"], best["b"])
    total_bytes = base_bytes + order_bytes

    return {
        "raw_bytes": len(raw_chunk),
        "digits": n,
        "freq_l1": freq_l1,
        "prep_seconds": round(prep_s, 3),
        "coarse_seconds": round(coarse_s, 3),
        "fine_seconds": round(fine_s, 3),
        "coarse_seeds": coarse_seeds,
        "coarse_k_samples": coarse_k_samples,
        "top_seed_count": top_seed_count,
        "fine_k_radius": fine_k_radius,
        "max_k": max_k,
        "best": best,
        "exact": bool(best["exact"]),
        "base_bytes": base_bytes,
        "order_bytes": order_bytes,
        "total_bytes": total_bytes,
        "ratio": round(len(raw_chunk) / total_bytes, 3) if total_bytes else 0.0,
        "top_coarse": finalists,
        "top_fine": sorted(fine_rows, key=lambda row: (row["mismatch"], -row["fixed"]))[: min(12, len(fine_rows))],
        "target_hash": hashlib.sha256(raw_chunk).hexdigest(),
    }


def run(path: Path, chunk_bytes: int, chunk_index: int, coarse_seeds: int, coarse_k_samples: int, top_seed_count: int, fine_k_radius: int, max_k: int, rng_seed: int) -> dict[str, Any]:
    raw = path.read_bytes()
    chunk = extract_chunk(raw, chunk_bytes, chunk_index)

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V31 — SENDER-SIDE SEED SEARCH                        ║")
    print("║  coarse seed jump + fine k refinement                      ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print(f"\nFile: {path}")
    print(f"Chunk bytes: {chunk_bytes:,}  chunk_index={chunk_index}")
    print(f"Chunk raw bytes: {len(chunk):,}")

    result = search_affine_seed_engine(
        raw_chunk=chunk,
        coarse_seeds=coarse_seeds,
        coarse_k_samples=coarse_k_samples,
        top_seed_count=top_seed_count,
        fine_k_radius=fine_k_radius,
        max_k=max_k,
        rng_seed=rng_seed,
    )

    best = result["best"]
    print(f"  Digits: {result['digits']:,}  freq_L1={result['freq_l1']:,}")
    print(f"  Prep: {result['prep_seconds']}s  coarse: {result['coarse_seconds']}s  fine: {result['fine_seconds']}s")
    print(f"  Best seed={best['seed']}  a={best['a']}  b={best['b']}  k={best['k']}")
    print(f"  Best mismatch={best['mismatch']:,}  fixed={best['fixed']:,}  exact={'YES' if best['exact'] else 'NO'}")
    print(f"  Packet estimate: base={result['base_bytes']}B  order={result['order_bytes']}B  total={result['total_bytes']}B")
    print(f"  Ratio: {result['ratio']:.2f}x")

    if result["top_coarse"]:
        print("\n  Top coarse seeds:")
        for row in result["top_coarse"][: min(8, len(result['top_coarse']))]:
            print(
                f"    seed={row['seed']:>10}  k={row['k']:>6}  mm={row['mismatch']:>8,}  "
                f"fixed={row['fixed']:>6,}  exact={'Y' if row['exact'] else 'N'}"
            )

    if result["top_fine"]:
        print("\n  Top fine candidates:")
        for row in result["top_fine"][: min(8, len(result['top_fine']))]:
            print(
                f"    seed={row['seed']:>10}  k={row['k']:>6}  mm={row['mismatch']:>8,}  "
                f"fixed={row['fixed']:>6,}  exact={'Y' if row['exact'] else 'N'}"
            )

    return result


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="RIDE V31 — sender-side seed+k search")
    parser.add_argument("file", help="File to probe")
    parser.add_argument("--chunk-bytes", type=int, default=10_240, help="Chunk size in bytes")
    parser.add_argument("--chunk-index", type=int, default=0, help="Chunk index")
    parser.add_argument("--coarse-seeds", type=int, default=96, help="Seed count for coarse scan")
    parser.add_argument("--coarse-k-samples", type=int, default=24, help="Sparse k samples per seed")
    parser.add_argument("--top-seeds", type=int, default=8, help="Top seeds to refine")
    parser.add_argument("--fine-k-radius", type=int, default=48, help="Fine local radius around best coarse k")
    parser.add_argument("--max-k", type=int, default=2048, help="Cap on k search")
    parser.add_argument("--rng-seed", type=int, default=42, help="Master RNG seed for seed proposals")
    parser.add_argument("--json-out", help="Optional JSON output")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    result = run(
        Path(args.file).expanduser(),
        chunk_bytes=args.chunk_bytes,
        chunk_index=args.chunk_index,
        coarse_seeds=args.coarse_seeds,
        coarse_k_samples=args.coarse_k_samples,
        top_seed_count=args.top_seeds,
        fine_k_radius=args.fine_k_radius,
        max_k=args.max_k,
        rng_seed=args.rng_seed,
    )
    if args.json_out:
        json_path = Path(args.json_out).expanduser()
        json_path.write_text(json.dumps(result, indent=2))
        print(f"\nJSON report written to {json_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
