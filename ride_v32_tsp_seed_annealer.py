#!/usr/bin/env python3
"""
RIDE V32 - TSP-informed seed annealer.
# v1.0 — 2026-04-13 — mile-guided SA, displacement-biased seed mutation

THE KEY DIFFERENCES FROM V31
-----------------------------
v31 used raw mismatch as energy and pure random seed mutation.
It found no gradient in seed space — mismatch stayed at ~87%.

This version:
1. Uses MILE as energy — mile measures minimum transpositions still needed,
   which is a richer gradient than mismatch. Mile decreases only when sigma^k
   actually resolves cycles, not just shuffles digits around.

2. Displacement-biased sigma construction — instead of pure FY, we construct
   sigma to preferentially move positions that are far from their target.
   Both encoder and decoder can reproduce this from (seed, source_coords, k).
   The seed controls the random choices; the displacement map is derived from
   source (shared K-coords) and the partial reconstruction state.

3. Multi-stage: after each accepted move, recompute the displacement map and
   bias the next sigma construction toward the remaining wrong positions.

4. Sigma family: displacement-sorted FY
   - Sort positions by |i - target_pos[i]| descending (most displaced first)
   - Apply FY shuffle only within groups of similarly-displaced positions
   - Result: sigma preferentially moves the most-displaced digits
   - Decoder can reproduce: knows source coords + reconstruction state

THE RECIPE
----------
Recipe = K-coords + delta + [(seed_1, k_1), (seed_2, k_2), ...]
Each (seed, k) pair corresponds to one annealing-accepted stage.
Decoder: for each (seed_i, k_i): regenerate sigma from seed_i + current state,
         apply sigma^k_i times, verify hash at end.

Note: the sigma depends on the CURRENT STATE at decode time, which evolves
stage by stage. This is fine — both encoder and decoder process stages in
the same order with the same current state at each step.
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
from ride_v13_canterbury_recipe_bench import build_perm_target_to_source, permutation_cycle_mile
from ride_v2_kpog_encoder import decompose_cycles


# ---------------------------------------------------------------------------
# Mile computation (exact, via cycle decomposition)
# ---------------------------------------------------------------------------

def compute_mile(current: list[int], target: list[int]) -> int:
    perm = list(build_perm_target_to_source(bytearray(target), bytearray(current)))
    mile, _ = permutation_cycle_mile(perm)
    return mile


# ---------------------------------------------------------------------------
# Displacement-biased sigma construction
# ---------------------------------------------------------------------------

def displacement_biased_sigma(
    current: np.ndarray,
    target: np.ndarray,
    n: int,
    seed: int,
) -> np.ndarray:
    """
    Build a sigma that preferentially moves positions with large displacement.

    Strategy:
    1. For each wrong position i, compute displacement = distance to where its
       digit needs to end up (approximate: position of matching digit in target)
    2. Sort wrong positions by displacement descending
    3. Apply seeded FY shuffle within bands of similarly-displaced positions
    4. Fixed positions stay fixed

    Both encoder and decoder can reproduce this from:
    - seed (transmitted in recipe)
    - current state (both sides have it at each decode stage)
    - target multiset (both sides know the K-source + delta)

    Note: target digit VALUES at each position are known to decoder via K-source.
    The decoder has the target arrangement as the GOAL — that's what it's reconstructing.
    But at decode time it doesn't know which specific digit value belongs at each
    position... WAIT. The decoder IS trying to reconstruct the target.

    Revised strategy: use only information available to decoder:
    - current state (known)
    - K-source (known, it's the source)
    - The mismatch positions (positions where current != source, but decoder
      doesn't know target yet)

    Actually simpler: the decoder has source (K-source) not target.
    Use displacement from SOURCE sorted order as the bias.
    Sort positions by how far current[i] is from source[i].
    This is computable from current state alone — no target needed.
    """
    rng = np.random.default_rng(seed)

    # Mismatch positions: where current differs from source (decoder knows source)
    # Actually decoder knows source = K-source. Target is what we're building toward.
    # Use: positions where current digit is not in the right "neighbourhood"
    # Simple proxy: positions sorted by current digit value distance from position's
    # "natural" value in a sorted arrangement.

    # Simplest decoder-reproducible bias: sort positions by current digit value
    # This groups same-valued digits together, which helps resolve the frequency layer
    # But we want ORDER resolution...

    # Best decoder-reproducible approach: sort positions by their index in the
    # source arrangement. Positions that haven't moved much from source stay together;
    # positions that differ most get shuffled more aggressively.

    # For now: pure displacement from sorted order (decoder-reproducible)
    sorted_order = np.argsort(np.argsort(current))  # rank of each digit
    natural_pos = np.arange(n)
    displacement = np.abs(sorted_order.astype(np.int64) - natural_pos.astype(np.int64))

    # Sort positions by displacement descending, apply FY within quartile bands
    sorted_indices = np.argsort(-displacement)  # most displaced first

    sigma = np.arange(n, dtype=np.int64)
    band_size = max(1, n // 4)

    for band_start in range(0, n, band_size):
        band_end = min(band_start + band_size, n)
        band = sorted_indices[band_start:band_end].copy()
        rng.shuffle(band)
        sigma[sorted_indices[band_start:band_end]] = band

    return sigma


def make_fy_sigma(n: int, seed: int) -> np.ndarray:
    return np.random.default_rng(seed & 0xFFFFFFFFFFFFFFFF).permutation(n).astype(np.int64)


def apply_sigma_once(arr: np.ndarray, sigma: np.ndarray) -> np.ndarray:
    result = np.empty(len(arr), dtype=arr.dtype)
    result[sigma] = arr
    return result


def best_k_for_sigma_mile(
    current_list: list[int],
    target_list: list[int],
    sigma: np.ndarray,
    max_k: int,
) -> tuple[int, int, list[int]]:
    """
    Apply sigma^1..max_k, return (best_k, best_mile, best_state) using mile as energy.
    """
    current_arr = np.array(current_list, dtype=np.uint8)
    best_mile = compute_mile(current_list, target_list)
    best_k = 0
    best_state = current_list[:]

    state_arr = current_arr.copy()
    for k in range(1, max_k + 1):
        state_arr = apply_sigma_once(state_arr, sigma)
        state_list = state_arr.tolist()
        mile = compute_mile(state_list, target_list)
        if mile < best_mile:
            best_mile = mile
            best_k = k
            best_state = state_list[:]

    return best_k, best_mile, best_state


def best_k_for_sigma_mismatch(
    current: np.ndarray,
    target: np.ndarray,
    sigma: np.ndarray,
    max_k: int,
) -> tuple[int, int, np.ndarray]:
    """Fast mismatch-based search (no cycle decomposition needed)."""
    best_mm = int(np.sum(current != target))
    best_k = 0
    best_arr = current.copy()

    state = current.copy()
    for k in range(1, max_k + 1):
        result = np.empty(len(state), dtype=state.dtype)
        result[sigma] = state
        state = result
        mm = int(np.sum(state != target))
        if mm < best_mm:
            best_mm = mm
            best_k = k
            best_arr = state.copy()

    return best_k, best_mm, best_arr


# ---------------------------------------------------------------------------
# Main annealer
# ---------------------------------------------------------------------------

def run(raw: bytes, max_k: int, n_iterations: int, initial_temp: float,
        cooling_rate: float, use_mile: bool, seed_master: int = 42) -> dict:

    t0 = time.perf_counter()
    source_list, target_list, params, freq_l1 = materialise_source_and_target(raw)
    n = len(target_list)
    source = np.array(source_list, dtype=np.uint8)
    target = np.array(target_list, dtype=np.uint8)
    prep_time = time.perf_counter() - t0

    print(f"  n={n:,}  freq_L1={freq_l1:,}  prep={prep_time:.2f}s")
    print(f"  max_k={max_k}  n_iterations={n_iterations:,}  T0={initial_temp}")
    print(f"  energy={'mile (slow but rich)' if use_mile else 'mismatch (fast)'}")
    print()

    rng = random.Random(seed_master)
    current_arr = source.copy()
    current_list = source_list[:]

    # Initial energy
    if use_mile:
        current_energy = compute_mile(current_list, target_list)
        energy_label = "mile"
    else:
        current_energy = int(np.sum(current_arr != target))
        energy_label = "mm"

    best_energy = current_energy
    best_arr = current_arr.copy()
    best_seed = 0
    best_k = 0
    stage_recipe = []  # list of (seed, k) pairs accepted

    temperature = initial_temp
    improvements = 0
    metropolis_accepts = 0
    last_print = time.perf_counter()

    print(f"  Start: {energy_label}={current_energy:,}  T={temperature:.2f}")

    for iteration in range(n_iterations):
        if best_energy == 0:
            break

        seed = rng.randint(0, 2**64 - 1)

        # Build displacement-biased sigma from current state
        sigma = displacement_biased_sigma(current_arr, target, n, seed & 0xFFFFFFFFFFFFFFFF)

        # Find best k
        if use_mile:
            k, energy_after, state_after_list = best_k_for_sigma_mile(
                current_list, target_list, sigma, max_k
            )
            state_after_arr = np.array(state_after_list, dtype=np.uint8)
        else:
            k, energy_after, state_after_arr = best_k_for_sigma_mismatch(
                current_arr, target, sigma, max_k
            )
            state_after_list = state_after_arr.tolist()

        if k == 0:
            temperature *= cooling_rate
            continue

        # Accept/reject
        delta = energy_after - current_energy
        accepted = False
        if delta < 0:
            accepted = True
            improvements += 1
        elif temperature > 1e-12 and delta > 0:
            prob = math.exp(-delta / temperature)
            if rng.random() < prob:
                accepted = True
                metropolis_accepts += 1

        if accepted:
            current_arr = state_after_arr
            current_list = state_after_list
            current_energy = energy_after
            stage_recipe.append((seed, k))

            if energy_after < best_energy:
                best_energy = energy_after
                best_arr = state_after_arr.copy()
                best_seed = seed
                best_k = k

        temperature *= cooling_rate

        now = time.perf_counter()
        if now - last_print > 5.0 or best_energy == 0:
            elapsed = now - t0
            rate = (iteration + 1) / elapsed
            mm = int(np.sum(current_arr != target))
            print(f"  iter={iteration+1:,}  {energy_label}={current_energy:,}  "
                  f"mm={mm:,} ({100*mm/n:.1f}%)  "
                  f"T={temperature:.4f}  stages={len(stage_recipe)}  "
                  f"impr={improvements}  {rate:.0f} iter/s  {elapsed:.1f}s")
            last_print = now
            sys.stdout.flush()

    elapsed = time.perf_counter() - t0
    final_mm = int(np.sum(current_arr != target))

    # Recipe: one (seed, k) per accepted stage
    pos_bits = math.ceil(math.log2(max(n, 2)))
    k_bits = math.ceil(math.log2(max(max_k + 1, 2)))
    seed_bits = 64
    recipe_bits_per_stage = seed_bits + k_bits
    total_recipe_bits = len(stage_recipe) * recipe_bits_per_stage
    overhead_bits = 193
    total_bits = overhead_bits + total_recipe_bits
    file_bits = len(raw) * 8
    ratio = file_bits / total_bits if total_bits > 0 else 0

    exact = final_mm == 0
    verify_hash = ""
    if exact:
        verify_hash = hashlib.sha256(current_arr.tobytes()).hexdigest()[:16]

    print(f"\n  {'='*60}")
    print(f"  SUMMARY")
    print(f"  Iterations:       {n_iterations:,}")
    print(f"  Accepted stages:  {len(stage_recipe)}")
    print(f"  Improvements:     {improvements}")
    print(f"  Metropolis:       {metropolis_accepts}")
    print(f"  Time:             {elapsed:.1f}s")
    print(f"  Final {energy_label}:      {current_energy:,}")
    print(f"  Final mismatch:   {final_mm:,}  ({100*final_mm/n:.2f}%)")
    print(f"  Recipe:           {len(stage_recipe)} x (seed64 + k{k_bits}) = {total_recipe_bits} bits = {total_recipe_bits//8} bytes")
    print(f"  Total w/ K:       {total_bits} bits = {total_bits//8} bytes")
    print(f"  File:             {len(raw):,} bytes")
    print(f"  Ratio:            {ratio:.1f}:1  {'(EXACT)' if exact else '(residual remains)'}")
    if exact:
        print(f"  Hash:             {verify_hash}")

    return {
        "file_bytes": len(raw),
        "n_digits": n,
        "final_energy": current_energy,
        "final_mismatch": final_mm,
        "stage_recipe": [(s, k) for s, k in stage_recipe],
        "total_recipe_bits": total_recipe_bits,
        "ratio": round(ratio, 2),
        "exact": exact,
        "elapsed": round(elapsed, 1),
    }


def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument("files", nargs="+")
    p.add_argument("--max-k", type=int, default=10)
    p.add_argument("--iterations", type=int, default=5000)
    p.add_argument("--temp", type=float, default=200.0)
    p.add_argument("--cooling", type=float, default=0.9990)
    p.add_argument("--mile", action="store_true",
                   help="Use mile as energy (slow but richer gradient)")
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--json-out")
    return p.parse_args()


def main():
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V32 — TSP-INFORMED SEED ANNEALER                     ║")
    print("║  Displacement-biased sigma, mile energy, multi-stage       ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    all_results = []
    for f in args.files:
        path = Path(f).expanduser()
        print(f"\n{'='*72}")
        print(f"  File: {path.name}  ({path.stat().st_size:,} bytes)")
        print(f"{'='*72}")
        result = run(path.read_bytes(), args.max_k, args.iterations,
                     args.temp, args.cooling, args.mile, args.seed)
        all_results.append(result)

    if args.json_out:
        import json
        with open(args.json_out, "w") as fh:
            json.dump(all_results, fh, indent=2)
        print(f"\nResults written to {args.json_out}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
