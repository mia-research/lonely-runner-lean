#!/usr/bin/env python3
"""
RIDE V30 - Chunk exact replication benchmark.

Tests chunk-local exact replication with strict hash gating.

Goal:
  - split a file into fixed-size chunks
  - run the current non-rank order engine on each chunk
  - accept success only when reconstructed bytes hash exactly
  - estimate current instruction bytes for successful and unsuccessful chunks

This is the honest interim-product boundary probe.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from ride_v13_canterbury_recipe_bench import (
    encode_svarint,
    encode_uvarint,
    leading_zero_bytes,
    materialize_bytes_from_decimal,
)
from ride_v19_pivot_cycle_orbit import materialise_source
from ride_v24_order_family_harness import (
    AnnealedHybridFamily,
    AnnealedHybridV2Family,
    AffineOrbitFamily,
    FisherOrbitFamily,
    LaneBlockOrbitFamily,
    better,
    residual_stats,
)


def estimate_step_bytes(chosen_family: str, inner: dict[str, Any]) -> int:
    if chosen_family == "affine_index":
        return (
            1
            + len(encode_uvarint(int(inner["a"])))
            + len(encode_uvarint(int(inner["b"])))
            + len(encode_uvarint(int(inner["k"])))
        )

    if chosen_family == "fixed_fisher_yates":
        return (
            1
            + len(encode_uvarint(int(inner["seed"])))
            + len(encode_uvarint(int(inner["k"])))
        )

    if chosen_family == "lane_block":
        mode = inner["mode"]
        total = 2
        if mode == "lane":
            total += len(encode_uvarint(int(inner["stride"])))
            total += len(encode_svarint(int(inner["k"])))
            return total
        if mode == "block":
            op = inner["op"]
            total += 1
            for value in op[1:]:
                total += len(encode_uvarint(abs(int(value))))
            return total
        return total

    if chosen_family == "cycle_arc":
        return (
            1
            + len(encode_uvarint(int(inner["cycle_index"])))
            + len(encode_uvarint(int(inner["pivot"])))
            + len(encode_uvarint(int(inner["prefix_macros"])))
        )

    return 1


def estimate_base_bytes(params: tuple[int, int, int, int], delta: list[int], raw: bytes) -> int:
    k_bytes = sum(len(encode_uvarint(value)) for value in params)
    delta_bytes = sum(len(encode_svarint(value)) for value in delta)
    meta_bytes = len(encode_uvarint(len(raw))) + len(encode_uvarint(leading_zero_bytes(raw)))
    hash_bytes = 32
    return k_bytes + delta_bytes + meta_bytes + hash_bytes


def build_family(name: str, raw: bytes, n: int):
    base_families = {
        "fixed_fisher_yates": FisherOrbitFamily(n, raw),
        "affine_index": AffineOrbitFamily(n, raw),
        "lane_block": LaneBlockOrbitFamily(),
    }
    if name == "annealed_hybrid":
        return AnnealedHybridFamily(["affine_index", "lane_block"], base_families, raw)
    if name == "annealed_hybrid_v2":
        return AnnealedHybridV2Family(base_families, raw)
    if name in base_families:
        return base_families[name]
    raise ValueError(f"unknown family: {name}")


def run_chunk(raw: bytes, family_name: str, stages: int) -> dict[str, Any]:
    try:
        source_digits, target_digits, params, delta, freq_l1 = materialise_source(raw)
    except Exception as exc:  # noqa: BLE001
        return {
            "raw_bytes": len(raw),
            "family": family_name,
            "exact": False,
            "materialise_error": str(exc),
            "base_bytes": None,
            "order_bytes": None,
            "total_bytes": None,
            "ratio": None,
            "steps": [],
        }
    family = build_family(family_name, raw, len(target_digits))
    if hasattr(family, "reset"):
        family.reset()

    current = list(source_digits)
    current_stats = residual_stats(current, list(target_digits))
    accepted_steps: list[dict[str, Any]] = []

    for stage in range(1, stages + 1):
        next_state, meta = family.stage(current, list(target_digits), current_stats)
        next_stats = residual_stats(next_state, list(target_digits))
        improved = next_state != current and better(next_stats, current_stats)
        accepted = bool(meta.get("accepted", improved)) if meta.get("family", "").startswith("annealed_") else improved
        if improved:
            current = next_state
            current_stats = next_stats
        accepted_steps.append(
            {
                "stage": stage,
                "accepted": accepted,
                "improved": improved,
                "mile": current_stats.mile,
                "fixed": current_stats.fixed,
                "mismatch": current_stats.mismatch,
                "meta": meta,
            }
        )
        if current == list(target_digits):
            break

    exact = False
    reconstructed_hash = None
    reconstruct_error = None
    try:
        rebuilt = materialize_bytes_from_decimal(bytearray(current), len(raw), leading_zero_bytes(raw))
        reconstructed_hash = hashlib.sha256(rebuilt).hexdigest()
        exact = rebuilt == raw and reconstructed_hash == hashlib.sha256(raw).hexdigest()
    except Exception as exc:  # noqa: BLE001
        reconstruct_error = str(exc)

    base_bytes = estimate_base_bytes(params, delta, raw)
    order_bytes = 0
    for step in accepted_steps:
        meta = step["meta"]
        if not step["improved"]:
            continue
        if meta["family"] in {"annealed_hybrid", "annealed_hybrid_v2"}:
            order_bytes += estimate_step_bytes(meta["chosen_family"], meta["inner"])
        else:
            inner_family = meta["family"]
            order_bytes += estimate_step_bytes(inner_family, meta)
    total_bytes = base_bytes + order_bytes

    return {
        "raw_bytes": len(raw),
        "digits": len(target_digits),
        "freq_l1": freq_l1,
        "family": family_name,
        "stages_run": len(accepted_steps),
        "final_mile": current_stats.mile,
        "final_fixed": current_stats.fixed,
        "final_mismatch": current_stats.mismatch,
        "exact": exact,
        "base_bytes": base_bytes,
        "order_bytes": order_bytes,
        "total_bytes": total_bytes,
        "ratio": round(len(raw) / total_bytes, 3) if total_bytes else 0.0,
        "reconstruct_error": reconstruct_error,
        "reconstructed_hash": reconstructed_hash,
        "target_hash": hashlib.sha256(raw).hexdigest(),
        "steps": accepted_steps,
    }


def chunk_iter(raw: bytes, chunk_bytes: int, chunk_limit: int | None):
    count = 0
    for start in range(0, len(raw), chunk_bytes):
        if chunk_limit is not None and count >= chunk_limit:
            break
        chunk = raw[start:start + chunk_bytes]
        if not chunk:
            break
        yield count, start, chunk
        count += 1


def run_file(path: Path, chunk_sizes: list[int], family_name: str, stages: int, chunk_limit: int | None) -> dict[str, Any]:
    raw = path.read_bytes()
    all_results: dict[str, Any] = {
        "file": str(path),
        "family": family_name,
        "stages": stages,
        "chunk_sizes": {},
    }

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V30 — CHUNK EXACT REPLICATION BENCH                  ║")
    print("║  accept only exact hash matches                            ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print(f"\nFile: {path}")
    print(f"Raw bytes: {len(raw):,}")
    print(f"Family: {family_name}  stages={stages}")

    for chunk_bytes in chunk_sizes:
        print(f"\n{'=' * 72}")
        print(f"Chunk size: {chunk_bytes:,} bytes")
        print(f"{'=' * 72}")
        chunk_rows: list[dict[str, Any]] = []
        solved = 0
        for chunk_index, start, chunk in chunk_iter(raw, chunk_bytes, chunk_limit):
            result = run_chunk(chunk, family_name, stages)
            result["chunk_index"] = chunk_index
            result["offset"] = start
            chunk_rows.append(result)
            if result["exact"]:
                solved += 1
            status = "EXACT" if result["exact"] else "miss"
            if result.get("materialise_error"):
                print(
                    f"  chunk={chunk_index:>2}  bytes={len(chunk):>6,}  materialise_error={result['materialise_error']}  miss",
                    flush=True,
                )
            else:
                print(
                    f"  chunk={chunk_index:>2}  bytes={len(chunk):>6,}  "
                    f"mile={result['final_mile']:>8,}  mismatch={result['final_mismatch']:>8,}  "
                    f"packet={result['total_bytes']:>4}B  ratio={result['ratio']:>7.2f}x  {status}",
                    flush=True,
                )

        total = len(chunk_rows)
        exact_ratios = [row["ratio"] for row in chunk_rows if row["exact"] and row["ratio"] is not None]
        packet_values = [row["total_bytes"] for row in chunk_rows if row["total_bytes"] is not None]
        ratio_values = [row["ratio"] for row in chunk_rows if row["ratio"] is not None]
        avg_packet = sum(packet_values) / len(packet_values) if packet_values else 0.0
        avg_ratio = sum(ratio_values) / len(ratio_values) if ratio_values else 0.0
        summary = {
            "chunks_tested": total,
            "chunks_exact": solved,
            "exact_rate": (solved / total) if total else 0.0,
            "avg_packet_bytes": round(avg_packet, 2),
            "avg_ratio": round(avg_ratio, 3),
            "avg_exact_ratio": round(sum(exact_ratios) / len(exact_ratios), 3) if exact_ratios else None,
            "rows": chunk_rows,
        }
        all_results["chunk_sizes"][str(chunk_bytes)] = summary
        print(
            f"  summary: exact={solved}/{total}  avg_packet={avg_packet:.1f}B  avg_ratio={avg_ratio:.2f}x",
            flush=True,
        )

    return all_results


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="RIDE V30 — chunk exact replication benchmark")
    parser.add_argument("file", help="File to chunk-test")
    parser.add_argument("--chunk-sizes", default="256,512,1024,2048,4096,10240", help="Comma-separated chunk sizes in bytes")
    parser.add_argument("--chunk-limit", type=int, default=1, help="Max chunks to test per size")
    parser.add_argument("--family", default="annealed_hybrid", choices=["annealed_hybrid", "annealed_hybrid_v2", "affine_index", "lane_block"], help="Order family")
    parser.add_argument("--stages", type=int, default=4, help="Stages per chunk")
    parser.add_argument("--json-out", help="Optional JSON report path")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    chunk_sizes = [int(part.strip()) for part in args.chunk_sizes.split(",") if part.strip()]
    result = run_file(
        Path(args.file).expanduser(),
        chunk_sizes=chunk_sizes,
        family_name=args.family,
        stages=args.stages,
        chunk_limit=args.chunk_limit,
    )
    if args.json_out:
        json_path = Path(args.json_out).expanduser()
        json_path.write_text(json.dumps(result, indent=2))
        print(f"\nJSON report written to {json_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
