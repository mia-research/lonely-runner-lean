#!/usr/bin/env python3
"""
RIDE V33 - Fresh affine family: re-seed (a,b) from current state at every stage.
# v1.0 — 2026-04-13 — fix for affine stall: generate new (a,b) pairs each stage

THE PROBLEM WITH V24 AFFINE
----------------------------
AffineOrbitFamily generates 12 (a,b) pairs ONCE at construction from raw hash.
After stage 1 finds the best k for those 12 sigmas, subsequent stages re-evaluate
the same 12 — stalling because the orbit structure hasn't changed.

THE FIX
--------
FreshAffineFamily regenerates (a,b) pairs at every stage, seeded from:
  hash(current_state)

Both encoder and decoder have identical current_state at each stage (they apply
the same accepted (a,b,k) in order), so this is fully decoder-reproducible.

The recipe per stage: (a, b, k) — about 3 × ceil(log2(n)) bits ≈ 36 bits.
No seed needs to be transmitted — decoder derives (a,b) from current state hash.

WHAT THIS TESTS
---------------
Can a continuously-fresh affine family maintain per-stage improvement beyond
stage 1? If yes, the recipe size per unit of mile reduction is:
  ~36 bits / (mile reduction per stage)

Compare to single-swap recipe: 24 bits / 1 mile = 24 bits/mile
Fresh affine target: 36 bits / N mile where N >> 1
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
import time
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
MIAI = Path("/Users/trentpalelei/MIAI")
for candidate in (HERE, MIAI):
    s = str(candidate)
    if candidate.exists() and s not in sys.path:
        sys.path.insert(0, s)

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(10_000_000)

from ride_v16_whole_file_orbit_steps import PCG32
from ride_v18_cycle_rsn import materialise_source_and_target
from ride_v24_order_family_harness import (
    K_CANDIDATES,
    ResidualStats,
    affine_sigma,
    apply_perm_power,
    better,
    coprime_multiplier,
    decompose_perm,
    raw_hash_seed,
    residual_stats,
    stats_energy,
    stats_key,
)


# ---------------------------------------------------------------------------
# Fresh affine family — new (a,b) per stage from current state hash
# ---------------------------------------------------------------------------

FRESH_AFFINE_COUNT = 64     # How many (a,b) pairs to try per stage
FRESH_AFFINE_TOP_KS = 8     # How many k values to try per sigma
FRESH_K_EXTRA_MAX = 512     # Additional k values from cycle length fractions


def state_seed(state: list[int]) -> int:
    """Derive a seed from current state — same on encoder and decoder."""
    digest = hashlib.sha256(bytes(state)).digest()
    return int.from_bytes(digest[:8], 'little')


def fresh_affine_candidates(
    current: list[int],
    target: list[int],
    current_stats: ResidualStats,
    n: int,
    n_affine: int = FRESH_AFFINE_COUNT,
    top_ks: int = FRESH_AFFINE_TOP_KS,
) -> list[tuple[list[int], ResidualStats, dict[str, Any]]]:
    """
    Generate fresh (a,b) pairs from current state hash and evaluate them.
    Returns candidates sorted by stats_key (best first).
    """
    seed = state_seed(current)
    rng = PCG32(seed)
    candidates = []

    for _ in range(n_affine):
        a = coprime_multiplier(rng, n)
        b = rng.next_uniform(n) if n > 0 else 0
        sigma = affine_sigma(n, a, b)
        cycles = decompose_perm(sigma)
        cycle_lengths = sorted((len(c) for c in cycles), reverse=True)[:4]
        k_values = sorted(
            set(K_CANDIDATES)
            | {
                v
                for length in cycle_lengths
                for v in (length // 4, length // 2, (3 * length) // 4, length - 1)
                if 0 < v <= FRESH_K_EXTRA_MAX
            }
        )

        for k in k_values[:top_ks]:
            if k == 0:
                continue
            candidate = apply_perm_power(current, sigma, cycles, k)
            cstats = residual_stats(candidate, target)
            meta = {"family": "fresh_affine", "a": a, "b": b, "k": k,
                    "state_seed": seed}
            candidates.append((candidate, cstats, meta))

    candidates.sort(key=lambda item: stats_key(item[1]))
    return candidates


# ---------------------------------------------------------------------------
# Multi-stage runner
# ---------------------------------------------------------------------------

def run(raw: bytes, n_stages: int, n_affine: int, top_ks: int) -> dict:
    t0 = time.perf_counter()
    source_digits, target_digits, params, l1 = materialise_source_and_target(raw)
    n = len(target_digits)
    prep_time = time.perf_counter() - t0

    print(f"  n={n:,}  freq_L1={l1:,}  prep={prep_time:.2f}s")
    print(f"  n_affine={n_affine}  top_ks={top_ks}  stages={n_stages}")
    print()
    print(f"  {'Stage':>5}  {'Mile':>7}  {'Fixed':>6}  {'MM':>6}  "
          f"{'a':>6}  {'b':>6}  {'k':>4}  {'Bits':>5}  {'Time':>5}")
    print(f"  {'-----':>5}  {'-------':>7}  {'------':>6}  {'------':>6}  "
          f"{'------':>6}  {'------':>6}  {'----':>4}  {'-----':>5}  {'-----':>5}")

    current = list(source_digits)
    init_stats = residual_stats(current, target_digits)
    print(f"  {'init':>5}  {init_stats.mile:>7,}  {init_stats.fixed:>6,}  "
          f"{init_stats.mismatch:>6,}  {'':>6}  {'':>6}  {'':>4}  {'':>5}")

    stage_results = []
    total_recipe_bits = 0
    pos_bits = math.ceil(math.log2(max(n, 2)))

    for stage_idx in range(1, n_stages + 1):
        t_stage = time.perf_counter()
        current_stats = residual_stats(current, target_digits)
        if current_stats.mile == 0:
            print(f"\n  Exact reconstruction at stage {stage_idx}!")
            break

        candidates = fresh_affine_candidates(
            current, target_digits, current_stats, n, n_affine, top_ks
        )

        best_state = current
        best_stats = current_stats
        best_meta: dict[str, Any] = {}

        for cstate, cstats, meta in candidates:
            if better(cstats, best_stats):
                best_state = cstate
                best_stats = cstats
                best_meta = meta

        improved = better(best_stats, current_stats)
        current = best_state
        stage_time = time.perf_counter() - t_stage

        # Recipe bits for this stage: (a, b, k) — decoder derives state_seed independently
        a = best_meta.get("a", 0)
        b = best_meta.get("b", 0)
        k = best_meta.get("k", 0)
        stage_bits = pos_bits + pos_bits + math.ceil(math.log2(max(k + 1, 2))) if improved else 0
        total_recipe_bits += stage_bits

        marker = "***" if improved else "   "
        print(f"  {stage_idx:>5}  {best_stats.mile:>7,}  {best_stats.fixed:>6,}  "
              f"{best_stats.mismatch:>6,}  {a:>6}  {b:>6}  {k:>4}  "
              f"{stage_bits:>5}  {stage_time:>4.1f}s  {marker}")
        sys.stdout.flush()

        stage_results.append({
            "stage": stage_idx,
            "improved": improved,
            "mile": best_stats.mile,
            "fixed": best_stats.fixed,
            "mismatch": best_stats.mismatch,
            "a": a, "b": b, "k": k,
            "recipe_bits": stage_bits,
        })

        if not improved:
            print(f"\n  No improvement at stage {stage_idx} — stopping.")
            break

    final_stats = residual_stats(current, target_digits)
    file_bits = len(raw) * 8
    overhead_bits = 193
    total_bits = overhead_bits + total_recipe_bits
    ratio = file_bits / total_bits if total_bits > 0 else 0

    print(f"\n  {'='*60}")
    print(f"  SUMMARY")
    print(f"  Stages run:     {len(stage_results)}")
    print(f"  Final mile:     {final_stats.mile:,}")
    print(f"  Final mismatch: {final_stats.mismatch:,}  ({100*final_stats.mismatch/n:.2f}%)")
    print(f"  Recipe bits:    {total_recipe_bits} = {total_recipe_bits//8} bytes")
    print(f"  Total w/ K:     {total_bits} bits = {total_bits//8} bytes")
    print(f"  File:           {len(raw):,} bytes")
    print(f"  Ratio:          {ratio:.1f}:1")
    print(f"  Bits/mile:      {total_recipe_bits/(init_stats.mile - final_stats.mile):.2f}"
          if init_stats.mile > final_stats.mile else "  Bits/mile:      n/a")

    return {
        "file_bytes": len(raw),
        "n_digits": n,
        "init_mile": init_stats.mile,
        "final_mile": final_stats.mile,
        "final_mismatch": final_stats.mismatch,
        "total_recipe_bits": total_recipe_bits,
        "ratio": round(ratio, 2),
        "stages": stage_results,
    }


def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument("files", nargs="+")
    p.add_argument("--stages", type=int, default=50)
    p.add_argument("--n-affine", type=int, default=64,
                   help="Fresh (a,b) pairs to try per stage (default 64)")
    p.add_argument("--top-ks", type=int, default=8,
                   help="k values to try per sigma (default 8)")
    p.add_argument("--json-out")
    return p.parse_args()


def main():
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V33 — FRESH AFFINE FAMILY                            ║")
    print("║  Re-seed (a,b) from current state each stage               ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    all_results = []
    for f in args.files:
        path = Path(f).expanduser()
        print(f"\n{'='*72}")
        print(f"  File: {path.name}  ({path.stat().st_size:,} bytes)")
        print(f"{'='*72}")
        result = run(path.read_bytes(), args.stages, args.n_affine, args.top_ks)
        all_results.append(result)

    if args.json_out:
        with open(args.json_out, "w") as fh:
            json.dump(all_results, fh, indent=2)
        print(f"\nResults written to {args.json_out}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
