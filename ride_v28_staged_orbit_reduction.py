#!/usr/bin/env python3
"""
RIDE V28 - Staged seed+k orbit reduction at file scale.
# v1.1 — 2026-04-13 — numpy hot path to make file-scale runs tractable

THE MODEL
---------
Recipe = K-coords + delta + [(seed_1, k_1), (seed_2, k_2), ...]
No permutation description transmitted. Decoder regenerates sigma from seed,
applies sigma^k, verifies with hash.

SIGMA FAMILY: SHORT-ORBIT BLOCK PERMUTATIONS
---------------------------------------------
Divide n positions into B blocks of size W = n//B.
  - Within-block cyclic rotation by r steps  (order = W/gcd(r,W))
  - Block-level rotation by s positions       (order = B/gcd(s,B))
  - Combined order divides lcm of the two    -> fits in ~18 bits

apply_k is O(n) via numpy roll — fast enough for file scale.

WHAT WE MEASURE
---------------
  - Mismatch curve per stage
  - Where reduction stalls (< stall_threshold for 3 consecutive stages)
  - Total recipe bits vs file size -> ratio
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
# Numpy block-rotation sigma — O(n) apply_k
# ---------------------------------------------------------------------------

def make_block_sigma(n: int, n_blocks: int, seed: int) -> tuple[int, int]:
    """Return (block_r, block_s) for given seed."""
    rng = random.Random(seed)
    W = n // n_blocks
    block_r = rng.randint(1, W - 1) if W > 1 else 0
    block_s = rng.randint(1, n_blocks - 1) if n_blocks > 1 else 0
    return block_r, block_s


def apply_block_sigma_k(arr: np.ndarray, n: int, n_blocks: int,
                         block_r: int, block_s: int, k: int) -> np.ndarray:
    """
    Apply sigma^k to arr using numpy — O(n).
    Effective rotations after k steps:
      eff_r = (block_r * k) % W   (within-block)
      eff_s = (block_s * k) % B   (block-level)
    """
    W = n // n_blocks
    B = n_blocks
    eff_r = (block_r * k) % W
    eff_s = (block_s * k) % B

    # Reshape to (B, W), apply within-block roll, then block-level roll
    body = arr[:B * W].reshape(B, W)
    # Within-block rotation: roll each row by eff_r
    if eff_r != 0:
        body = np.roll(body, eff_r, axis=1)
    # Block-level rotation: roll rows by eff_s
    if eff_s != 0:
        body = np.roll(body, eff_s, axis=0)
    result = np.empty(n, dtype=arr.dtype)
    result[:B * W] = body.ravel()
    result[B * W:] = arr[B * W:]   # tail unchanged
    return result


def sigma_order(n: int, n_blocks: int, block_r: int, block_s: int) -> int:
    from math import gcd
    W = n // n_blocks
    B = n_blocks
    r_ord = W // gcd(block_r, W) if block_r > 0 else 1
    s_ord = B // gcd(block_s, B) if block_s > 0 else 1
    # lcm
    g = gcd(r_ord, s_ord)
    return r_ord * s_ord // g


# ---------------------------------------------------------------------------
# Single stage
# ---------------------------------------------------------------------------

def search_stage(
    current: np.ndarray,
    target: np.ndarray,
    n: int,
    n_blocks: int,
    n_seeds: int,
    stage_idx: int,
    rng_master: random.Random,
) -> tuple[np.ndarray, dict]:
    t0 = time.perf_counter()
    mm_before = int(np.sum(current != target))

    best_seed = 0
    best_k = 0
    best_mm = mm_before
    best_arr = current.copy()

    W = n // n_blocks

    for _ in range(n_seeds):
        seed = rng_master.randint(0, 2**32 - 1)
        block_r, block_s = make_block_sigma(n, n_blocks, seed)
        ord_ = sigma_order(n, n_blocks, block_r, block_s)
        max_k = min(ord_, W + n_blocks)

        for k in range(1, max_k + 1):
            candidate = apply_block_sigma_k(current, n, n_blocks, block_r, block_s, k)
            mm = int(np.sum(candidate != target))
            if mm < best_mm:
                best_mm = mm
                best_seed = seed
                best_k = k
                best_arr = candidate

    reduction = (mm_before - best_mm) / mm_before if mm_before > 0 else 0.0
    block_r, block_s = make_block_sigma(n, n_blocks, best_seed)
    ord_ = sigma_order(n, n_blocks, block_r, block_s)
    k_bits = math.ceil(math.log2(max(ord_, 2)))
    seed_r_bits = math.ceil(math.log2(max(W, 2)))
    seed_s_bits = math.ceil(math.log2(max(n_blocks, 2)))
    recipe_bits = seed_r_bits + seed_s_bits + k_bits

    return best_arr, {
        "stage": stage_idx,
        "seed": best_seed,
        "k": best_k,
        "mismatch_before": mm_before,
        "mismatch_after": best_mm,
        "reduction": round(reduction, 4),
        "sigma_order": ord_,
        "recipe_bits": recipe_bits,
        "search_time": round(time.perf_counter() - t0, 2),
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def run(raw: bytes, n_blocks: int, n_seeds: int, max_stages: int,
        stall_threshold: float, seed_master: int = 42) -> dict:

    t0 = time.perf_counter()
    source_list, target_list, params, freq_l1 = materialise_source_and_target(raw)
    n = len(target_list)
    source = np.array(source_list, dtype=np.uint8)
    target = np.array(target_list, dtype=np.uint8)
    prep_time = time.perf_counter() - t0

    W = n // n_blocks
    print(f"  n={n:,}  W={W}  B={n_blocks}  freq_L1={freq_l1:,}  prep={prep_time:.2f}s")
    print(f"  n_seeds={n_seeds}  max_k_per_seed={W + n_blocks}")
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
            current, target, n, n_blocks, n_seeds, stage_idx, rng_master
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
                print(f"\n  STALL: < {stall_threshold:.0%} reduction for 3 stages. This is where it breaks.")
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

    if final_mm > 0 and stage_results:
        last_rate = stage_results[-1]["reduction"]
        if last_rate > 0.001:
            mm = final_mm
            est = len(stage_results)
            bits_per_stage = stage_results[-1]["recipe_bits"]
            while mm > 0 and est < 100000:
                mm = int(mm * (1 - last_rate))
                est += 1
            proj_bits = overhead_bits + est * bits_per_stage
            print(f"  Projected stages to 0 (at last rate): ~{est}")
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
    p.add_argument("--blocks", type=int, default=1000)
    p.add_argument("--seeds", type=int, default=200)
    p.add_argument("--stages", type=int, default=40)
    p.add_argument("--stall", type=float, default=0.02)
    p.add_argument("--json-out")
    return p.parse_args()


def main():
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V28 — STAGED SEED+K ORBIT REDUCTION (numpy)          ║")
    print("║  Measure mismatch reduction rate. Find where it breaks.    ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    all_results = []
    for f in args.files:
        path = Path(f).expanduser()
        print(f"\n{'='*72}")
        print(f"  File: {path.name}  ({path.stat().st_size:,} bytes)")
        print(f"{'='*72}")
        result = run(path.read_bytes(), args.blocks, args.seeds,
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
