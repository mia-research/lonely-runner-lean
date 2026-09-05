#!/usr/bin/env python3
"""
RIDE V34 - Sender-side affine -> optional meso -> Fisher-Yates chain.

The main change from V33 is architectural:
  - the middle hop is optional
  - FY can attack the affine state directly
  - lane is tried only as one possible meso refinement, not a mandatory hop

This matches the current working hypothesis:
  K-coords + delta get us into the right ingredient space,
  affine gets us close,
  FY may be the best last-mile family,
  and meso structure should only be inserted when it helps.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path
from typing import Any

from ride_v13_canterbury_recipe_bench import leading_zero_bytes
from ride_v19_pivot_cycle_orbit import materialise_source
from ride_v31_sender_seed_search import estimate_base_bytes, estimate_order_bytes, extract_chunk
from ride_v33_affine_lane_fy_chain import (
    exact_hit_bytes,
    fy_order_bytes,
    lane_order_bytes,
    score_candidate,
    search_affine_candidates,
    search_fy_candidates,
    search_lane_candidates,
)


def none_meso_row(state: bytearray, target: bytearray, raw_len: int, zero_prefix: int, raw_hash: str) -> dict[str, Any]:
    mismatch, neg_fixed = score_candidate(state, target)
    return {
        "family": "none",
        "seed": 0,
        "k": 0,
        "mismatch": mismatch,
        "fixed": -neg_fixed,
        "exact": exact_hit_bytes(state, raw_len, zero_prefix, raw_hash),
        "state": bytearray(state),
    }


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
    meso_reports: list[dict[str, Any]] = []
    fy_reports: list[dict[str, Any]] = []

    for affine_index, affine_row in enumerate(affine["candidates"][:beam_affine]):
        affine_state = affine_row["state"]
        meso_candidates: list[dict[str, Any]] = [
            none_meso_row(affine_state, target, len(raw_chunk), zero_prefix, raw_hash)
        ]

        if lane_seeds > 0 and beam_lane > 0:
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
            meso_reports.append(
                {
                    "affine_index": affine_index,
                    "from_affine": {k: v for k, v in affine_row.items() if k != "state"},
                    "best_lane": lane["best"],
                    "seconds": lane["seconds"],
                }
            )
            meso_candidates.extend(lane["candidates"][:beam_lane])

        for meso_index, meso_row in enumerate(meso_candidates):
            meso_state = meso_row["state"]
            fy = search_fy_candidates(
                source=meso_state,
                target=target,
                raw_len=len(raw_chunk),
                zero_prefix=zero_prefix,
                raw_hash=raw_hash,
                seeds=fy_seeds,
                shortlist=1,
                rng_seed=(
                    rng_seed
                    ^ 0x5A5A5A5A
                    ^ int(affine_row["seed"])
                    ^ (int(meso_row["seed"]) << 1)
                    ^ (meso_index << 12)
                ),
            )
            fy_reports.append(
                {
                    "affine_index": affine_index,
                    "meso_index": meso_index,
                    "from_affine": {k: v for k, v in affine_row.items() if k != "state"},
                    "from_meso": {k: v for k, v in meso_row.items() if k != "state"},
                    "best": fy["best"],
                    "seconds": fy["seconds"],
                }
            )
            candidate = {
                "affine": {k: v for k, v in affine_row.items() if k != "state"},
                "meso": {k: v for k, v in meso_row.items() if k != "state"},
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
    meso = best_chain["meso"]
    meso_bytes = 0 if meso["family"] == "none" else lane_order_bytes(meso["seed"], meso["k"])
    order_bytes = (
        estimate_order_bytes(best_chain["affine"]["seed"], best_chain["affine"]["k"], best_chain["affine"]["a"], best_chain["affine"]["b"])
        + meso_bytes
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
        "meso_reports": meso_reports[: min(8, len(meso_reports))],
        "fy_reports": fy_reports[: min(16, len(fy_reports))],
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
    meso = result["best_chain"]["meso"]
    fy = result["best_chain"]["fy"]

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V34 — AFFINE -> OPTIONAL MESO -> FY                 ║")
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
    if meso["family"] == "none":
        print(
            f"Meso:   none  mismatch={meso['mismatch']:,}  fixed={meso['fixed']:,}"
        )
    else:
        print(
            f"Meso:   {meso['family']}  seed={meso['seed']}  stride={meso['stride']}  k={meso['k']}  "
            f"mismatch={meso['mismatch']:,}  fixed={meso['fixed']:,}"
        )
    print(
        f"FY:     seed={fy['seed']}  k={fy['k']}  mismatch={fy['mismatch']:,}  "
        f"fixed={fy['fixed']:,}  exact={'YES' if fy['exact'] else 'NO'}"
    )
    print(f"Packet estimate: base={result['base_bytes']}B  order={result['order_bytes']}B  total={result['total_bytes']}B")
    print(f"Ratio: {result['ratio']:.2f}x")
    return result


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="RIDE V34 — affine -> optional meso -> FY")
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
    parser.add_argument("--fy-seeds", type=int, default=48)
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
