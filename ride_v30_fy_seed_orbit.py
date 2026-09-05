#!/usr/bin/env python3
"""
RIDE V30 - Staged Fisher-Yates seed + step orbit reduction.
# v1.0 — 2026-04-13 — FY with fixed seed; apply sigma^k by replaying k times

THE MODEL
---------
Recipe = K-coords + delta + [(seed_1, k_1), (seed_2, k_2), ...]
Decoder: regenerate sigma from seed (FY shuffle), apply sigma k times.
No permutation transmitted. Decoder reconstructs from shared (seed, k).

WHY FY INSTEAD OF AFFINE
--------------------------
Affine sigma (v29) stalled at ~87% mismatch — same as block-rotation (v28).
Root cause: any generic sigma applied to 87% mismatched digits moves roughly
87% of already-wrong digits to new wrong positions. Small net gain.

FY produces a truly random permutation with random cycle structure.
The v27 finding was that stressed cycles have geometric(p=0.38) gap distribution —
i.e., cycle membership LOOKS like a random subset. If that's true, a random
permutation of the right length might align better with the actual disorder.

This tests the hypothesis: does the random structure of FY help compared to
structured sigmas (block-rotation, affine)?

APPLYING σ^k:
  No closed form for FY. We replay the FY shuffle k times.
  O(n*k) per evaluation. With n=2293 (abstract) and k<=50, this is tractable.
  For file scale (n=895k) we cap max_k at a small number.

SEEDED FY:
  Both encoder and decoder use numpy.random.Generator seeded identically.
  sigma = np.random.default_rng(seed).permutation(n)
  sigma_k = apply sigma k times = sigma composed with itself k times.

FAST sigma^k via matrix exponentiation analogy:
  sigma^k = sigma composed k times.
  We can precompute sigma^2 = sigma[sigma], sigma^4 = sigma^2[sigma^2], etc.
  Then compose in O(n * log k) rather than O(n * k). Use this for large k.
"""

from __future__ import annotations

import argparse
import math
import random
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
MIAI = Path("/Users/trentpalelei/MIAI")
for candidate in (HERE, MIAI):
    s = str(candidate)
    if candidate.exists() and s not in sys.path:
        sys.path.insert(0, s)

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(10_000_000)

from ride_v18_cycle_rsn import materialise_source_and_target


# ---------------------------------------------------------------------------
# FY sigma generation and fast power-by-squaring
# ---------------------------------------------------------------------------

def make_fy_sigma(n: int, seed: int) -> np.ndarray:
    """Generate FY permutation of [0..n) from seed."""
    return np.random.default_rng(seed).permutation(n)


def perm_power(sigma: np.ndarray, k: int) -> np.ndarray:
    """Compute sigma^k via repeated squaring. O(n log k)."""
    n = len(sigma)
    result = np.arange(n, dtype=np.int64)  # identity
    base = sigma.astype(np.int64)
    while k > 0:
        if k & 1:
            result = base[result]
        base = base[base]
        k >>= 1
    return result


def apply_sigma_k(arr: np.ndarray, sigma_k: np.ndarray) -> np.ndarray:
    """Apply permutation: new[sigma_k[i]] = arr[i]."""
    result = np.empty(len(arr), dtype=arr.dtype)
    result[sigma_k] = arr
    return result


# ---------------------------------------------------------------------------
# Single stage search
# ---------------------------------------------------------------------------

def search_stage(
    current: np.ndarray,
    target: np.ndarray,
    n: int,
    n_seeds: int,
    max_k: int,
    stage_idx: int,
    rng_master: random.Random,
) -> tuple[np.ndarray, dict]:
    t0 = time.perf_counter()
    mm_before = int(np.sum(current != target))

    best_seed = 0
    best_k = 0
    best_mm = mm_before
    best_arr = current.copy()

    for _ in range(n_seeds):
        seed = rng_master.randint(0, 2**32 - 1)
        sigma = make_fy_sigma(n, seed)

        # Precompute sigma^1 through sigma^max_k efficiently
        # For small max_k we just compose iteratively and evaluate each step
        # For large max_k use squaring to jump to each k
        # Here: evaluate k=1,2,...,max_k by iterative composition (O(n*max_k) per seed)
        sigma_cur = sigma.copy()
        for k in range(1, max_k + 1):
            if k > 1:
                sigma_cur = sigma[sigma_cur]  # compose: sigma^k = sigma o sigma^(k-1)
            candidate = apply_sigma_k(current, sigma_cur)
            mm = int(np.sum(candidate != target))
            if mm < best_mm:
                best_mm = mm
                best_seed = seed
                best_k = k
                best_arr = candidate

    reduction = (mm_before - best_mm) / mm_before if mm_before > 0 else 0.0

    k_bits = math.ceil(math.log2(max(best_k + 1, 2)))
    seed_bits = 32
    recipe_bits = seed_bits + k_bits

    return best_arr, {
        "stage": stage_idx,
        "seed": best_seed,
        "k": best_k,
        "mismatch_before": mm_before,
        "mismatch_after": best_mm,
        "reduction": round(reduction, 4),
        "recipe_bits": recipe_bits,
        "search_time": round(time.perf_counter() - t0, 2),
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def run(raw: bytes, n_seeds: int, max_k: int, max_stages: int,
        stall_threshold: float, seed_master: int = 42) -> dict:

    t0 = time.perf_counter()
    source_list, target_list, params, freq_l1 = materialise_source_and_target(raw)
    n = len(target_list)
    source = np.array(source_list, dtype=np.uint8)
    target = np.array(target_list, dtype=np.uint8)
    prep_time = time.perf_counter() - t0

    print(f"  n={n:,}  freq_L1={freq_l1:,}  prep={prep_time:.2f}s")
    print(f"  n_seeds={n_seeds}  max_k={max_k}  (O(n*seeds*max_k) per stage)")
    print()
    print(f"  {'Stage':>5}  {'MM_before':>10}  {'MM_after':>10}  {'Reduction':>10}  "
          f"{'k':>6}  {'RecBits':>8}  {'Time':>6}")
    print(f"  {'-'*5}  {'-'*10}  {'-'*10}  {'-'*10}  {'-'*6}  {'-'*8}  {'-'*6}")

    rng_master = random.Random(seed_master)
    current = source.copy()
    stage_results = []
    total_recipe_bits = 0
    stall_count = 0

    for stage_idx in range(max_stages):
        mm_now = int(np.sum(current != target))
        if mm_now == 0:
            print(f"\n  Zero mismatch reached at stage {stage_idx}!")
            break

        current, result = search_stage(
            current, target, n, n_seeds, max_k, stage_idx, rng_master
        )
        stage_results.append(result)
        total_recipe_bits += result["recipe_bits"]

        print(f"  {result['stage']:>5}  {result['mismatch_before']:>10,}  "
              f"{result['mismatch_after']:>10,}  {result['reduction']:>9.1%}  "
              f"{result['k']:>6}  {result['recipe_bits']:>8}  {result['search_time']:>5.1f}s")
        sys.stdout.flush()

        if result["reduction"] < stall_threshold:
            stall_count += 1
            if stall_count >= 3:
                print(f"\n  STALL: < {stall_threshold:.0%} reduction for 3 stages.")
                break
        else:
            stall_count = 0

    final_mm = int(np.sum(current != target))
    file_bits = len(raw) * 8
    overhead_bits = 193  # K-coords + delta
    total_bits = overhead_bits + total_recipe_bits
    ratio = file_bits / total_bits if total_bits > 0 else 0

    print(f"\n  {'='*60}")
    print(f"  SUMMARY")
    print(f"  Stages:         {len(stage_results)}")
    print(f"  Final mismatch: {final_mm:,}  ({100*final_mm/n:.2f}% of digits)")
    print(f"  Recipe:         {total_recipe_bits} bits = {total_recipe_bits//8} bytes")
    print(f"  Total (w/ K):   {total_bits} bits = {total_bits//8} bytes")
    print(f"  File:           {len(raw):,} bytes")
    print(f"  Ratio:          {ratio:.1f}:1  {'(mismatch=0, VALID)' if final_mm==0 else '(residual remains)'}")

    if final_mm > 0 and stage_results and stage_results[-1]["reduction"] > 0.001:
        last_rate = stage_results[-1]["reduction"]
        mm = final_mm
        est = len(stage_results)
        bits_per_stage = stage_results[-1]["recipe_bits"]
        while mm > 0 and est < 1_000_000:
            mm = int(mm * (1 - last_rate))
            est += 1
        proj_bits = overhead_bits + est * bits_per_stage
        print(f"  Projected stages to 0 (at last rate): ~{est:,}")
        print(f"  Projected ratio: ~{file_bits/proj_bits:.0f}:1")

    return {
        "file_bytes": len(raw),
        "n_digits": n,
        "stages": len(stage_results),
        "final_mismatch": final_mm,
        "total_recipe_bits": total_recipe_bits,
        "ratio": round(ratio, 2),
        "stage_results": stage_results,
    }


def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument("files", nargs="+")
    p.add_argument("--seeds", type=int, default=200,
                   help="FY seeds to try per stage (default 200)")
    p.add_argument("--max-k", type=int, default=20,
                   help="Max steps to search per sigma (default 20; high k is O(n*k))")
    p.add_argument("--stages", type=int, default=40)
    p.add_argument("--stall", type=float, default=0.02)
    p.add_argument("--json-out")
    return p.parse_args()


def main():
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V30 — STAGED FISHER-YATES SEED + STEP ORBIT          ║")
    print("║  σ = FY(seed); apply σ^k; no permutation transmitted        ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    all_results = []
    for f in args.files:
        path = Path(f).expanduser()
        print(f"\n{'='*72}")
        print(f"  File: {path.name}  ({path.stat().st_size:,} bytes)")
        print(f"{'='*72}")
        result = run(path.read_bytes(), args.seeds, args.max_k,
                     args.stages, args.stall)
        all_results.append(result)

    if args.json_out:
        import json
        with open(args.json_out, "w") as fh:
            json.dump(all_results, fh, indent=2)
        print(f"\nResults written to {args.json_out}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
