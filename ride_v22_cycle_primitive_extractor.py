#!/usr/bin/env python3
"""
RIDE V22 - Cycle-native primitive extractor.

Phase 1 diagnostic pass for the next macro family:

  - start from the exact V18 cycle manifold plan
  - inspect stressed cycles on real whole-file targets
  - measure whether the route looks more like:
      * cycle-arc extraction
      * pivot-star chunk moves
      * cycle segment grammar

This script does not build a codec. It is intentionally read-only and
diagnostic: it tells us which cycle-native language the data is actually
asking for.
"""

from __future__ import annotations

import argparse
import math
import statistics
import sys
import time
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
MIAI = Path("/Users/trentpalelei/MIAI")
for candidate in (HERE, MIAI):
    candidate_str = str(candidate)
    if candidate.exists() and candidate_str not in sys.path:
        sys.path.insert(0, candidate_str)

from ride_v12_kmanifold_probe import binary_to_decimal_lossless
from ride_v13_canterbury_recipe_bench import build_perm_target_to_source, str_to_digits
from ride_v18_cycle_rsn import (
    build_rsn_cycle_plan,
    choose_cycle_pivot,
    cycle_stress,
    materialise_source_and_target,
    rotate_cycle_to_pivot,
)


ARC_THRESHOLDS = (1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096)
RUN_MIN = 4
TOP_CYCLES = 6


def median_int(values: list[int]) -> float:
    if not values:
        return 0.0
    return float(statistics.median(values))


def mean_int(values: list[int]) -> float:
    if not values:
        return 0.0
    return float(sum(values) / len(values))


def count_decimal_digits(raw: bytes) -> int:
    decimal = binary_to_decimal_lossless(raw)
    return len(decimal)


def sorted_positions_and_gaps(cycle: list[int], n: int) -> tuple[list[int], list[int]]:
    positions = sorted(cycle)
    if not positions:
        return [], []
    gaps: list[int] = []
    for idx in range(len(positions) - 1):
        gaps.append(positions[idx + 1] - positions[idx])
    gaps.append((positions[0] + n) - positions[-1])
    return positions, gaps


def arc_partition_lengths(positions: list[int], n: int, threshold: int) -> list[int]:
    if not positions:
        return []
    arcs: list[int] = []
    current = 1
    for idx in range(len(positions) - 1):
        gap = positions[idx + 1] - positions[idx]
        if gap <= threshold:
            current += 1
        else:
            arcs.append(current)
            current = 1
    wrap_gap = (positions[0] + n) - positions[-1]
    if wrap_gap <= threshold and arcs:
        arcs[0] += current
    elif wrap_gap <= threshold:
        arcs.append(current)
    else:
        arcs.append(current)
    return sorted(arcs, reverse=True)


def arc_metrics(cycle: list[int], n: int) -> dict:
    positions, gaps = sorted_positions_and_gaps(cycle, n)
    results: list[dict] = []
    best = None
    best_key = None

    for threshold in ARC_THRESHOLDS:
        arcs = arc_partition_lengths(positions, n, threshold)
        if not arcs:
            continue
        top1 = arcs[0]
        top3 = sum(arcs[:3])
        top5 = sum(arcs[:5])
        coverage3 = top3 / len(cycle)
        coverage5 = top5 / len(cycle)
        record = {
            "threshold": threshold,
            "arc_count": len(arcs),
            "top1": top1,
            "top3": top3,
            "top5": top5,
            "coverage3": coverage3,
            "coverage5": coverage5,
        }
        results.append(record)
        key = (coverage3, coverage5, -len(arcs), top1)
        if best is None or key > best_key:
            best = record
            best_key = key

    return {
        "gaps_median": median_int(gaps),
        "gaps_mean": mean_int(gaps),
        "gaps_max": max(gaps) if gaps else 0,
        "best": best,
        "all": results,
    }


def monotone_runs(seq: list[int]) -> list[int]:
    if len(seq) <= 1:
        return [len(seq)] if seq else []
    runs: list[int] = []
    start = 0
    direction = 0
    for idx in range(1, len(seq)):
        diff = seq[idx] - seq[idx - 1]
        sign = 0 if diff == 0 else (1 if diff > 0 else -1)
        if direction == 0:
            direction = sign
            continue
        if sign == 0 or sign == direction:
            continue
        runs.append(idx - start)
        start = idx - 1
        direction = sign
    runs.append(len(seq) - start)
    return runs


def arithmetic_runs(seq: list[int]) -> list[int]:
    if len(seq) <= 1:
        return [len(seq)] if seq else []
    runs: list[int] = []
    start = 0
    delta = None
    for idx in range(1, len(seq)):
        current = seq[idx] - seq[idx - 1]
        if delta is None:
            delta = current
            continue
        if current == delta:
            continue
        runs.append(idx - start)
        start = idx - 1
        delta = current
    runs.append(len(seq) - start)
    return runs


def run_lengths_summary(lengths: list[int], total: int) -> dict:
    if not lengths:
        return {
            "count": 0,
            "max": 0,
            "mean": 0.0,
            "cover_ge4": 0.0,
            "top3_cover": 0.0,
        }
    sorted_lengths = sorted(lengths, reverse=True)
    cover_ge4 = sum(length for length in lengths if length >= RUN_MIN) / total if total else 0.0
    top3_cover = sum(sorted_lengths[:3]) / total if total else 0.0
    return {
        "count": len(lengths),
        "max": max(lengths),
        "mean": mean_int(lengths),
        "cover_ge4": cover_ge4,
        "top3_cover": top3_cover,
    }


def ngram_reuse(values: list[int], width: int) -> dict:
    if len(values) < width:
        return {"distinct": 0, "repeat_occurrences": 0, "reuse_ratio": 0.0}
    grams = [tuple(values[idx : idx + width]) for idx in range(len(values) - width + 1)]
    counts = Counter(grams)
    repeat_occurrences = sum(count for count in counts.values() if count > 1)
    return {
        "distinct": len(counts),
        "repeat_occurrences": repeat_occurrences,
        "reuse_ratio": repeat_occurrences / len(grams) if grams else 0.0,
    }


def quantize_ratio(value: float, bins: int = 16) -> int:
    bounded = min(max(value, 0.0), 0.999999999)
    return int(bounded * bins)


def analyse_cycle(cycle: list[int], perm: list[int], n: int) -> dict:
    displacement, span, length = cycle_stress(cycle, perm)
    pivot = choose_cycle_pivot(cycle, perm)
    rotated = rotate_cycle_to_pivot(cycle, pivot)
    partners = list(reversed(rotated[1:]))
    partner_offsets = [partner - pivot for partner in partners]
    partner_abs = [abs(offset) for offset in partner_offsets]

    monotone = run_lengths_summary(monotone_runs(partners), len(partners))
    arithmetic = run_lengths_summary(arithmetic_runs(partners), len(partners))
    delta_runs = run_lengths_summary(arithmetic_runs(partner_offsets), len(partner_offsets))
    bigram = ngram_reuse(partner_offsets, 2)
    trigram = ngram_reuse(partner_offsets, 3)
    arc = arc_metrics(cycle, n)

    return {
        "length": length,
        "span": span,
        "displacement": displacement,
        "pivot": pivot,
        "pivot_bin16": quantize_ratio(pivot / n if n else 0.0),
        "pivot_offset_mean": mean_int(partner_abs),
        "pivot_offset_median": median_int(partner_abs),
        "partners": len(partners),
        "monotone": monotone,
        "arithmetic": arithmetic,
        "delta_runs": delta_runs,
        "bigram_reuse": bigram,
        "trigram_reuse": trigram,
        "arc": arc,
    }


def weighted_average(items: list[dict], key_fn, weight_key: str = "length") -> float:
    if not items:
        return 0.0
    total_weight = sum(item[weight_key] for item in items)
    if total_weight == 0:
        return 0.0
    return sum(key_fn(item) * item[weight_key] for item in items) / total_weight


def aggregate_metrics(cycle_metrics: list[dict]) -> dict:
    pivot_bins = Counter(item["pivot_bin16"] for item in cycle_metrics)
    top_pivot_bins = pivot_bins.most_common(4)
    pivot_concentration = sum(count for _bin, count in top_pivot_bins) / len(cycle_metrics) if cycle_metrics else 0.0

    weighted_arc3 = weighted_average(
        cycle_metrics,
        lambda item: item["arc"]["best"]["coverage3"] if item["arc"]["best"] else 0.0,
    )
    weighted_arc_count = weighted_average(
        cycle_metrics,
        lambda item: item["arc"]["best"]["arc_count"] if item["arc"]["best"] else 0.0,
    )
    weighted_monotone = weighted_average(cycle_metrics, lambda item: item["monotone"]["cover_ge4"])
    weighted_arithmetic = weighted_average(cycle_metrics, lambda item: item["arithmetic"]["cover_ge4"])
    weighted_delta_runs = weighted_average(cycle_metrics, lambda item: item["delta_runs"]["cover_ge4"])
    weighted_trigram = weighted_average(cycle_metrics, lambda item: item["trigram_reuse"]["reuse_ratio"])

    scores = {
        "cycle_arc_extraction": 0.60 * weighted_arc3 + 0.25 * min(1.0, pivot_concentration) + 0.15 * (1.0 / max(1.0, weighted_arc_count)),
        "pivot_star_chunk_move": 0.55 * weighted_monotone + 0.30 * weighted_arithmetic + 0.15 * min(1.0, pivot_concentration),
        "cycle_segment_grammar": 0.55 * weighted_trigram + 0.25 * weighted_delta_runs + 0.20 * weighted_monotone,
    }
    winner = max(scores, key=scores.get) if scores else "unknown"
    return {
        "pivot_bins": top_pivot_bins,
        "pivot_concentration": pivot_concentration,
        "weighted_arc3": weighted_arc3,
        "weighted_arc_count": weighted_arc_count,
        "weighted_monotone": weighted_monotone,
        "weighted_arithmetic": weighted_arithmetic,
        "weighted_delta_runs": weighted_delta_runs,
        "weighted_trigram": weighted_trigram,
        "scores": scores,
        "winner": winner,
    }


def format_count(value: float) -> str:
    if isinstance(value, int):
        return f"{value:,}"
    return f"{value:,.3f}"


def run_case(path: Path) -> dict:
    raw = path.read_bytes()
    n_bytes = len(raw)
    print(f"\n{'=' * 76}")
    print(f"  Cycle primitive extraction: {path.name}")
    print(f"{'=' * 76}")
    print(f"  Raw bytes: {n_bytes:,}")
    print(f"  Decimal digits: {count_decimal_digits(raw):,}")

    t0 = time.perf_counter()
    source_digits, target_digits, params, l1 = materialise_source_and_target(raw)
    prep_time = time.perf_counter() - t0

    t1 = time.perf_counter()
    perm = list(build_perm_target_to_source(bytearray(target_digits), bytearray(source_digits)))
    plan = build_rsn_cycle_plan(perm)
    cycle_metrics = [analyse_cycle(cycle, perm, len(target_digits)) for cycle in plan["cycles"] if len(cycle) > 1]
    cycle_metrics.sort(key=lambda item: (item["displacement"], item["span"], item["length"]), reverse=True)
    aggregate = aggregate_metrics(cycle_metrics)
    analyse_time = time.perf_counter() - t1

    print(f"  K params: v0={params[0]:,} a={params[1]:,} b={params[2]:,} v9={params[3]:,}")
    print(f"  Frequency delta L1: {l1:,}")
    print(f"  Non-trivial cycles: {len(cycle_metrics):,}")
    print(f"  Prep time: {prep_time:.2f}s")
    print(f"  Analyse time: {analyse_time:.2f}s")
    print("  Aggregate structure:")
    print(f"    pivot concentration (top 4 bins): {aggregate['pivot_concentration']:.3f}  bins={aggregate['pivot_bins']}")
    print(f"    weighted arc top-3 coverage: {aggregate['weighted_arc3']:.3f}")
    print(f"    weighted best arc count: {aggregate['weighted_arc_count']:.1f}")
    print(f"    weighted monotone coverage: {aggregate['weighted_monotone']:.3f}")
    print(f"    weighted arithmetic coverage: {aggregate['weighted_arithmetic']:.3f}")
    print(f"    weighted delta-run coverage: {aggregate['weighted_delta_runs']:.3f}")
    print(f"    weighted trigram reuse: {aggregate['weighted_trigram']:.3f}")
    print("  Candidate family scores:")
    for name, score in sorted(aggregate["scores"].items(), key=lambda item: item[1], reverse=True):
        print(f"    {name}: {score:.3f}")
    print(f"  Recommended first family: {aggregate['winner']}")

    top_cycles = cycle_metrics[:TOP_CYCLES]
    print("  Top stressed cycles:")
    for idx, item in enumerate(top_cycles, start=1):
        best_arc = item["arc"]["best"]
        arc_desc = "none"
        if best_arc:
            arc_desc = (
                f"thr={best_arc['threshold']} arcs={best_arc['arc_count']} "
                f"cov3={best_arc['coverage3']:.3f} cov5={best_arc['coverage5']:.3f}"
            )
        print(
            "    "
            f"#{idx} len={item['length']:,} span={item['span']:,} disp={item['displacement']:,} "
            f"pivot={item['pivot']:,} bin={item['pivot_bin16']} "
            f"monotone={item['monotone']['cover_ge4']:.3f} "
            f"arith={item['arithmetic']['cover_ge4']:.3f} "
            f"trigram={item['trigram_reuse']['reuse_ratio']:.3f} "
            f"arc[{arc_desc}]"
        )

    return {
        "path": str(path),
        "raw_bytes": n_bytes,
        "cycles": len(cycle_metrics),
        "aggregate": aggregate,
        "top_cycles": top_cycles,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Cycle-native primitive extractor")
    parser.add_argument("files", nargs="+", help="Whole files to inspect")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V22 - CYCLE PRIMITIVE EXTRACTOR                      ║")
    print("║  exact stressed-cycle diagnostics for macro-family choice  ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    for file_arg in args.files:
        run_case(Path(file_arg).expanduser())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
