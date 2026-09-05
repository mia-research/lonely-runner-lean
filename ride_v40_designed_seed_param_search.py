#!/usr/bin/env python3
# ride_v40_designed_seed_param_search.py
# v1.0 — 2026-04-15 — Part 2 of /Users/trentpalelei/.claude/plans/serialized-hugging-fairy.md
#
# Co-opts the TSP SA engine (extracted from
# /Users/trentpalelei/Desktop/TSP/lambda_function_37_original.py) to search
# over DESIGNED-SEED configuration spaces — i.e., small parameter tuples θ
# whose deterministic constructor σ(θ) produces permutations engineered to
# sit on the cycle-geometry manifold observed on real files (v18: 13-16
# huge stressed cycles; v27: geometric gap p≈0.377).
#
# Benchmark rungs:
#   Rung 0 — synthetic: each space vs. a target it constructed itself.
#   Rung 1 — text slice (v24 test bed).
#   Rung 2 — raw PDF page.
#   Rung 3 — LRC PDF full (the v28–v30 87% falsification target).
#
# Spaces:
#   raw_fy_seed     — v30 baseline, matched-budget control.
#   cycle_geometry  — engineered cycle sizes + geometric gaps.
#   hybrid_schedule — generalised v24 annealed_hybrid (affine/lane/rev/fy).
#   cycle_arc       — v23-style arcs with stride/direction (known-hard).
#
# Usage:
#   python ride_v40_designed_seed_param_search.py --quick      # smoke test
#   python ride_v40_designed_seed_param_search.py --rungs 0 1
#   python ride_v40_designed_seed_param_search.py --full

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from datetime import datetime
from pathlib import Path

import numpy as np

from ride_v40_lib.core import (
    apply_perm_np,
    file_hash,
    mile,
    mismatch_ratio,
    validate_permutation,
)
from ride_v40_lib.rungs import (
    Rung,
    build_synthetic_rung,
    load_lrc_pdf_rung,
    load_pdf_page_rung,
    load_text_slice_rung,
)
from ride_v40_lib.parallel import WorkItem, run_parallel
from ride_v40_lib.sa_kernel import SAConfig, SAResult, result_to_json, run_sa
from ride_v40_lib.spaces import (
    CycleArcSpace,
    CycleGeometrySpace,
    HybridScheduleSpace,
    RawFYSeedSpace,
)


LOGS_DIR = Path("/Users/trentpalelei/Desktop/Math Ex/logs")


def build_space(name: str, n: int):
    if name == "raw_fy_seed":
        return RawFYSeedSpace(n)
    if name == "cycle_geometry":
        return CycleGeometrySpace(n)
    if name == "hybrid_schedule":
        return HybridScheduleSpace(n)
    if name == "cycle_arc":
        return CycleArcSpace(n)
    raise ValueError(f"unknown space: {name}")


SPACE_NAMES = ("raw_fy_seed", "cycle_geometry", "hybrid_schedule", "cycle_arc")


def verify_exact_match(rung: Rung, sigma: np.ndarray) -> bool:
    """Apply sigma to source, check against target via hash (the oracle)."""
    if not np.issubdtype(sigma.dtype, np.integer):
        return False
    try:
        validate_permutation(sigma, rung.n)
    except ValueError:
        return False
    reconstructed = apply_perm_np(rung.source, sigma)
    # Convert to bytes identically on both sides
    src_bytes = rung.target.astype(np.uint8).tobytes()
    rec_bytes = reconstructed.astype(np.uint8).tobytes()
    return file_hash(src_bytes) == file_hash(rec_bytes)


def run_space_on_rung(space_name: str, rung: Rung, config: SAConfig,
                      n_runs: int) -> list[SAResult]:
    space = build_space(space_name, rung.n)
    results: list[SAResult] = []
    for run_id in range(n_runs):
        local_config = SAConfig(**{**config.__dict__, "rng_seed": config.rng_seed + run_id})
        result = run_sa(space, rung.target_perm, local_config,
                        energy_fn=mismatch_ratio, run_id=run_id)

        # Hash-oracle verification at the end (not per-iteration; too slow).
        # Reconstruct the best σ from best_theta.
        best_sigma = space.construct(
            _theta_from_json(space, result.best_theta_json)
        )
        result.exact_match = verify_exact_match(rung, best_sigma)
        if result.exact_match:
            print(f"[v40] *** EXACT MATCH on {rung.name} via {space_name} "
                  f"run_id={run_id} best_iter={result.best_iteration} ***")
        results.append(result)
    return results


def _theta_from_json(space, theta_json: dict):
    """Reconstruct θ from logged JSON so we can rebuild σ post-hoc."""
    name = space.name
    if name == "raw_fy_seed":
        from ride_v40_lib.spaces.raw_fy_seed import FYTheta
        return FYTheta(seed=theta_json["seed"])
    if name == "cycle_geometry":
        from ride_v40_lib.spaces.cycle_geometry import CycleGeomTheta
        return CycleGeomTheta(**theta_json)
    if name == "hybrid_schedule":
        from ride_v40_lib.spaces.hybrid_schedule import ScheduleTheta, Stage
        stages = tuple(Stage(family=s["family"], params=tuple(s["params"]))
                       for s in theta_json["stages"])
        return ScheduleTheta(stages=stages)
    if name == "cycle_arc":
        from ride_v40_lib.spaces.cycle_arc import Arc, CycleArcTheta
        arcs = tuple(Arc(**a) for a in theta_json["arcs"])
        return CycleArcTheta(arcs=arcs)
    raise ValueError(name)


def print_results_table(title: str, table: dict) -> None:
    """
    table: {rung_name: {space_name: list[SAResult]}}
    """
    print()
    print("=" * 92)
    print(title)
    print("=" * 92)
    header = f"{'rung':<26} {'space':<18} {'init_E':>8} {'best_E':>8} {'med_E':>8} {'min_E':>8} {'exact':>6} {'iters':>8}"
    print(header)
    print("-" * 100)
    for rung_name, by_space in table.items():
        for space_name, results in by_space.items():
            if not results:
                continue
            best_energies = [r.best_energy for r in results]
            any_exact = any(r.exact_match for r in results)
            median_best = float(np.median(best_energies))
            min_best = float(min(best_energies))
            iters_total = sum(r.n_iterations for r in results)
            init_E = float(np.mean([r.initial_energy for r in results]))
            print(f"{rung_name:<26} {space_name:<18} "
                  f"{init_E:>8.4f} {results[0].best_energy:>8.4f} "
                  f"{median_best:>8.4f} {min_best:>8.4f} "
                  f"{'YES' if any_exact else 'no':>6} {iters_total:>8,d}")
    print("=" * 100)


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--rungs", nargs="+", type=int, default=None,
                   help="Rung indices to run (0-3). Default: all available.")
    p.add_argument("--spaces", nargs="+", default=list(SPACE_NAMES),
                   help=f"θ-spaces to test. Default: all ({SPACE_NAMES}).")
    p.add_argument("--n-runs", type=int, default=3,
                   help="Independent SA runs per (space, rung). Default: 3.")
    p.add_argument("--budget-sec", type=float, default=900.0,
                   help="Wallclock per SA run (seconds). Default: 900 (15 min).")
    p.add_argument("--max-iter", type=int, default=20_000,
                   help="Max SA iterations per run. Default: 20,000.")
    p.add_argument("--initial-temp", type=float, default=0.5)
    p.add_argument("--cooling-rate", type=float, default=0.9995)
    p.add_argument("--restart-patience", type=int, default=3_000)
    p.add_argument("--rng-seed", type=int, default=42)
    p.add_argument("--synthetic-n", type=int, default=2_000,
                   help="Size of Rung 0 synthetic target. Default: 2,000.")
    p.add_argument("--quick", action="store_true",
                   help="Smoke test: Rung 0 only, 1 run per space, 1000 iters, 30s budget.")
    p.add_argument("--full", action="store_true",
                   help="All rungs, all spaces, 3 runs, 15min each.")
    p.add_argument("--output", type=Path, default=None,
                   help="Output JSON path. Default: logs/ride_v40_<timestamp>.json.")
    p.add_argument("--workers", type=int, default=None,
                   help="Parallel worker count. Default: (cpu_count - 1). "
                        "Set to 1 to force serial execution.")
    p.add_argument("--serial", action="store_true",
                   help="Force serial execution (equivalent to --workers 1).")
    return p.parse_args()


def main() -> int:
    args = parse_args()

    if args.quick:
        args.rungs = [0]
        args.n_runs = 1
        args.max_iter = 1_000
        args.budget_sec = 30.0
        args.synthetic_n = 1_000

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_path = args.output or (LOGS_DIR / f"ride_v40_{timestamp}.json")

    sa_config = SAConfig(
        initial_temp=args.initial_temp,
        cooling_rate=args.cooling_rate,
        min_temp=1e-9,
        max_iterations=args.max_iter,
        wallclock_budget_sec=args.budget_sec,
        restart_patience=args.restart_patience,
        restart_keep_best=True,
        rng_seed=args.rng_seed,
        log_every=max(100, args.max_iter // 40),
        early_stop_mismatch=0.0,
    )

    # Build rungs.
    all_rungs: list[Rung] = []
    wanted = args.rungs if args.rungs is not None else [0, 1, 2, 3]

    if 0 in wanted:
        # Rung 0 is built per-space: each θ-space's self-consistency test.
        # We handle it as a special case below.
        pass

    if 1 in wanted:
        r = load_text_slice_rung()
        if r is not None:
            all_rungs.append(r)
        else:
            print("[v40] Rung 1 (text_slice) unavailable; skipping.", file=sys.stderr)

    if 2 in wanted:
        r = load_pdf_page_rung()
        if r is not None:
            all_rungs.append(r)
        else:
            print("[v40] Rung 2 (pdf_page) unavailable; skipping.", file=sys.stderr)

    if 3 in wanted:
        r = load_lrc_pdf_rung()
        if r is not None:
            all_rungs.append(r)
        else:
            print("[v40] Rung 3 (lrc_pdf) unavailable; skipping.", file=sys.stderr)

    # Print plan summary.
    print("=" * 92)
    print(f"ride_v40  start={timestamp}  spaces={args.spaces}  "
          f"n_runs={args.n_runs}  budget={args.budget_sec:.0f}s/run  "
          f"max_iter={args.max_iter:,}")
    print("=" * 92)

    table: dict[str, dict[str, list[SAResult]]] = {}
    all_results: list[SAResult] = []

    # Build the full list of work items (one SA run each).
    work_items: list[WorkItem] = []
    # Each rung stores (rung_name, n, source, target) for later hash-oracle verify.
    rung_registry: dict[str, Rung] = {}

    # ---- Rung 0: synthetic self-consistency (per space) ----
    if 0 in wanted:
        print(f"\n[Rung 0] synthetic self-consistency (n={args.synthetic_n})")
        import random as _random
        for space_name in args.spaces:
            space = build_space(space_name, args.synthetic_n)
            seed_rng = _random.Random(args.rng_seed + 777)
            theta_truth = space.sample(seed_rng)
            truth_perm = space.construct(theta_truth)
            validate_permutation(truth_perm, args.synthetic_n)
            rung = build_synthetic_rung(space_name, truth_perm, args.synthetic_n)
            rung_registry[rung.name] = rung
            table.setdefault(rung.name, {})[space_name] = []
            for run_id in range(args.n_runs):
                work_items.append(WorkItem(
                    space_name=space_name,
                    rung_name=rung.name,
                    target_perm=rung.target_perm,
                    n=rung.n,
                    run_id=run_id,
                    sa_config=sa_config,
                ))

    # ---- Rungs 1-3: real files ----
    for rung in all_rungs:
        print(f"\n[{rung.name}] {rung.description} | n={rung.n:,}")
        rung_registry[rung.name] = rung
        for space_name in args.spaces:
            table.setdefault(rung.name, {})[space_name] = []
            for run_id in range(args.n_runs):
                work_items.append(WorkItem(
                    space_name=space_name,
                    rung_name=rung.name,
                    target_perm=rung.target_perm,
                    n=rung.n,
                    run_id=run_id,
                    sa_config=sa_config,
                ))

    # Dispatch.
    workers = 1 if args.serial else args.workers
    if workers == 1:
        print(f"\n[v40] running {len(work_items)} work items serially")
        completed: list[tuple[str, str, SAResult]] = []
        for item in work_items:
            space = build_space(item.space_name, item.n)
            from dataclasses import replace as _replace
            local_config = _replace(item.sa_config,
                                    rng_seed=item.sa_config.rng_seed + item.run_id)
            result = run_sa(space, item.target_perm, local_config,
                            energy_fn=mismatch_ratio, run_id=item.run_id)
            completed.append((item.space_name, item.rung_name, result))
    else:
        completed = run_parallel(work_items, max_workers=workers)

    # Hash-oracle verification + bucket into results table.
    for space_name, rung_name, result in completed:
        rung = rung_registry[rung_name]
        space = build_space(space_name, rung.n)
        best_sigma = space.construct(_theta_from_json(space, result.best_theta_json))
        result.exact_match = verify_exact_match(rung, best_sigma)
        if result.exact_match:
            print(f"[v40] *** EXACT MATCH on {rung_name} via {space_name} "
                  f"run_id={result.run_id} best_iter={result.best_iteration} ***")
        table[rung_name][space_name].append(result)
        all_results.append(result)

    # Summary.
    print_results_table("FINAL RESULTS (median of n_runs per cell)", table)

    # v30-wall comparison.
    print("\nCalibration against v30's 87% wall:")
    for rung_name, by_space in table.items():
        if "raw_fy_seed" not in by_space:
            continue
        baseline_med = float(np.median([r.best_energy for r in by_space["raw_fy_seed"]]))
        for space_name, results in by_space.items():
            if space_name == "raw_fy_seed":
                continue
            med = float(np.median([r.best_energy for r in results]))
            delta = baseline_med - med
            direction = "BETTER" if delta > 0.01 else ("WORSE" if delta < -0.01 else "tie")
            print(f"  {rung_name:<18} {space_name:<18} baseline={baseline_med:.4f} "
                  f"space={med:.4f} Δ={delta:+.4f} ({direction})")

    # Persist.
    meta = {
        "timestamp": timestamp,
        "args": {k: (str(v) if isinstance(v, Path) else v) for k, v in vars(args).items()},
        "sa_config": sa_config.__dict__,
        "rungs": [
            {"name": r.name, "description": r.description, "n": r.n,
             "raw_path": str(r.raw_path) if r.raw_path else None}
            for r in all_rungs
        ],
    }
    LOGS_DIR.mkdir(parents=True, exist_ok=True)
    payload = {
        "meta": meta,
        "table": {
            rung_name: {
                space_name: [result_to_json(r) for r in results]
                for space_name, results in by_space.items()
            }
            for rung_name, by_space in table.items()
        },
    }
    with out_path.open("w") as f:
        json.dump(payload, f, indent=2)
    print(f"\nResults written to: {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
