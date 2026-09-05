#!/usr/bin/env python3
"""
RIDE V29 - Staged affine sigma orbit reduction.
# v1.0 — 2026-04-13 — affine sigma replaces block-rotation; global reach

THE MODEL
---------
Recipe = K-coords + delta + [(a_1, b_1, k_1), (a_2, b_2, k_2), ...]
Decoder regenerates sigma from (a,b): σ(i) = (a*i + b) mod n
Applies σ^k: σ^k(i) = (a^k * i + b*(a^k-1)/(a-1)) mod n  [closed form, O(1) per position]
No permutation transmitted. Decoder reconstructs from shared K-coords + (a,b,k).

WHY AFFINE INSTEAD OF BLOCK-ROTATION
-------------------------------------
Block-rotation (v28) stalled immediately: it moves positions within their block,
but the stressed cycles have GLOBAL span (positions 0..895k appear in one cycle).
A block-local sigma can't resolve globally-scattered displacement.

Affine σ(i) = (a*i + b) mod n is a GLOBAL rearrangement:
  - Every position talks to every other position (for coprime a and n)
  - σ^k has closed-form: exponent k means applying the affine map k times
  - The orbit of any point under σ visits (n / cycle_length_of_a_in_Zn*) positions
  - We can scan k=1..ord(σ) efficiently since affine maps have computable order

APPLYING σ^k IN O(n) via numpy:
  σ^k(i) = (a^k * i + b * (a^k - 1) / (a - 1)) mod n  when a != 1
  σ^k(i) = (i + k*b) mod n                              when a == 1
Both computed vectorially on np.arange(n).

AFFINE SIGMA ORDER:
  ord(σ) = ord(a in Z/nZ*) = smallest k s.t. a^k ≡ 1 mod n
  For prime n: ord(a) divides n-1
  For composite n: ord(a) divides λ(n) (Carmichael function)
  We cap search at min(ord, MAX_K_SEARCH) to stay tractable.

WHAT WE MEASURE
---------------
  - Mismatch curve per stage
  - Where reduction stalls
  - Total recipe bits vs file size -> replication ratio
"""

from __future__ import annotations

import argparse
import hashlib
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
# Affine sigma — O(n) apply_k via numpy
# ---------------------------------------------------------------------------

def affine_order(a: int, n: int) -> int:
    """Multiplicative order of a mod n. Returns 1 if a=1."""
    if a == 1:
        return n  # translation by b has order n/gcd(b,n), but we handle separately
    k = 1
    cur = a % n
    while cur != 1 and k < n:
        cur = (cur * a) % n
        k += 1
    return k if cur == 1 else n


def apply_affine_k(arr: np.ndarray, n: int, a: int, b: int, k: int) -> np.ndarray:
    """
    Apply σ^k to arr where σ(i) = (a*i + b) mod n.
    σ^k(i) = (a^k * i + b*(a^k-1)/(a-1)) mod n  if a != 1
    σ^k(i) = (i + k*b) mod n                     if a == 1

    This gives us the new POSITION of element currently at index i.
    So result[sigma_k[i]] = arr[i], i.e. result = arr[inv_sigma_k].

    We want to APPLY the permutation (move arr[i] to where sigma says it goes):
      result[sigma_k(i)] = arr[i]
    Which is equivalent to: result = arr[argsort(sigma_k)] = arr[inv_sigma_k]
    But argsort on 900k is fast.

    Actually, for mismatch reduction we want:
      new_current = sigma_k applied to current
    meaning: new_current[i] = current[sigma_k^{-1}(i)]
    i.e., element at position j moves to position sigma_k(j)
    so new_current[sigma_k(j)] = current[j]

    We compute sigma_k as an index array and use it directly.
    """
    indices = np.arange(n, dtype=np.int64)

    if a == 1:
        # Pure translation: sigma^k(i) = (i + k*b) mod n
        ak_b = (k * b) % n
        sigma_k = (indices + ak_b) % n
    else:
        ak = pow(int(a), int(k), int(n))  # a^k mod n
        # b * (a^k - 1) * modinverse(a-1, n)
        try:
            inv_am1 = pow(int(a - 1), -1, int(n))
            offset = (int(b) * ((ak - 1) * inv_am1 % n)) % n
        except ValueError:
            # a-1 not invertible mod n — fall back to pure iteration (slow, only for edge cases)
            sigma_k = indices.copy()
            for _ in range(k):
                sigma_k = (a * sigma_k + b) % n
            sigma_k = sigma_k.astype(np.int64)
            result = np.empty(n, dtype=arr.dtype)
            result[sigma_k] = arr
            return result
        sigma_k = (ak * indices + offset) % n

    result = np.empty(n, dtype=arr.dtype)
    result[sigma_k] = arr
    return result


def affine_sigma_order(a: int, b: int, n: int) -> int:
    """Order of affine map σ(i)=(a*i+b) mod n as a permutation of Z/nZ."""
    if a == 1:
        # Pure shift: order = n / gcd(b, n)
        if b == 0:
            return 1
        return n // math.gcd(b, n)
    # General: order divides lcm(ord(a in Z/nZ*), something)
    # Upper bound: multiply ord_a by n (conservative but correct)
    ord_a = affine_order(a, n)
    return ord_a  # actual order divides ord_a * some factor; we search up to min(ord_a, cap)


# ---------------------------------------------------------------------------
# Seeded affine family — decoder-reproducible from (seed, n)
# ---------------------------------------------------------------------------

def make_affine_sigma(n: int, seed: int) -> tuple[int, int]:
    """
    Generate (a, b) for affine sigma from seed.
    a must be coprime with n to ensure bijection.
    Uses rejection sampling — fast in practice.
    """
    rng = random.Random(seed)
    for _ in range(1000):
        a = rng.randint(2, n - 1)
        if math.gcd(a, n) == 1:
            b = rng.randint(0, n - 1)
            return a, b
    # Fallback: a=1 (pure shift)
    b = rng.randint(1, n - 1)
    return 1, b


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
    best_a, best_b = 1, 0

    for _ in range(n_seeds):
        seed = rng_master.randint(0, 2**32 - 1)
        a, b = make_affine_sigma(n, seed)
        ord_ = affine_sigma_order(a, b, n)
        cap = min(ord_, max_k)

        for k in range(1, cap + 1):
            candidate = apply_affine_k(current, n, a, b, k)
            mm = int(np.sum(candidate != target))
            if mm < best_mm:
                best_mm = mm
                best_seed = seed
                best_k = k
                best_arr = candidate
                best_a, best_b = a, b

    reduction = (mm_before - best_mm) / mm_before if mm_before > 0 else 0.0

    # Recipe bits: seed (32 bits) + k (log2(max_k) bits)
    k_bits = math.ceil(math.log2(max(best_k + 1, 2)))
    seed_bits = 32
    recipe_bits = seed_bits + k_bits

    return best_arr, {
        "stage": stage_idx,
        "seed": best_seed,
        "a": best_a,
        "b": best_b,
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
    print(f"  n_seeds={n_seeds}  max_k={max_k}")
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
                   help="Affine sigma seeds to try per stage (default 200)")
    p.add_argument("--max-k", type=int, default=500,
                   help="Max k to search per sigma (default 500)")
    p.add_argument("--stages", type=int, default=40)
    p.add_argument("--stall", type=float, default=0.02)
    p.add_argument("--json-out")
    return p.parse_args()


def main():
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V29 — STAGED AFFINE SIGMA ORBIT REDUCTION            ║")
    print("║  Affine σ(i)=(a*i+b) mod n — global reach, O(n) apply_k   ║")
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
