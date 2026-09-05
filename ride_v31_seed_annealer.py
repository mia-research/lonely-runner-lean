#!/usr/bin/env python3
"""
RIDE V31 - Seed annealer: find (seed, k) such that sigma^k(source) = target.
# v1.0 — 2026-04-13 — simulated annealing over seed space

THE MODEL
---------
Recipe = K-coords + delta + (seed, k)
Decoder: regenerate sigma = FY(seed), apply k times, verify hash. Done.
The sender does the expensive search. The recipe stays tiny.

THE ANNEALER
------------
State: current seed S
Energy: mismatch(sigma_best_k(source), target)
  where best_k = argmin_k mismatch(sigma^k(source), target) for k in 1..max_k

Mutation: XOR seed with a random bitmask (neighbourhood search in seed space)
Accept: Metropolis criterion — always accept improvement, accept worsening
        with probability exp(-delta / T)
Temperature: geometric cooling T *= cooling_rate each iteration

If energy hits 0: exact reconstruction found. Recipe = (seed, k). Done.

WHY THIS IS DIFFERENT FROM v28-v30
------------------------------------
v28-v30 sampled random seeds independently. Each seed was evaluated in isolation.
There was no learning between seeds — no gradient, no memory.

The annealer treats seed space as a landscape and navigates it:
- Start from a good seed (hash-derived from K-source + target)
- Mutate and accept/reject based on energy
- Temperature allows escaping local minima early, then tightens
- The search budget goes to refining promising seeds, not random exploration

SIGMA FAMILY: Fisher-Yates (decoder-reproducible from seed)
  sigma = np.random.default_rng(seed).permutation(n)
  sigma^k via repeated composition, cached across k values

HASH VERIFICATION
-----------------
When mismatch = 0: verify with SHA-256 of the reconstructed digit sequence.
Recipe includes the hash for decoder-side verification.
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
# Sigma generation and application
# ---------------------------------------------------------------------------

def make_sigma(n: int, seed: int) -> np.ndarray:
    return np.random.default_rng(seed & 0xFFFFFFFFFFFFFFFF).permutation(n).astype(np.int64)


def best_k_for_sigma(
    source: np.ndarray,
    target: np.ndarray,
    sigma: np.ndarray,
    max_k: int,
) -> tuple[int, int, np.ndarray]:
    """
    Apply sigma^1 .. sigma^max_k to source, return (best_k, best_mm, best_arr).
    Iterative composition is O(n * max_k) but avoids re-generating sigma.
    """
    n = len(source)
    best_mm = int(np.sum(source != target))
    best_k = 0
    best_arr = source.copy()

    current = source.copy()
    sigma_cur = sigma.copy()

    for k in range(1, max_k + 1):
        # Apply sigma_cur as a permutation: new[sigma_cur[i]] = current[i]
        result = np.empty(n, dtype=current.dtype)
        result[sigma_cur] = current
        mm = int(np.sum(result != target))
        if mm < best_mm:
            best_mm = mm
            best_k = k
            best_arr = result.copy()
        current = result
        if k < max_k:
            sigma_cur = sigma[sigma_cur]  # sigma^(k+1) = sigma o sigma^k

    return best_k, best_mm, best_arr


# ---------------------------------------------------------------------------
# Seed mutation strategies
# ---------------------------------------------------------------------------

def mutate_seed(seed: int, rng: random.Random, temperature: float) -> int:
    """
    Mutate seed in a temperature-dependent way.
    High T: large jumps (flip many bits or jump far)
    Low T: small perturbations (flip 1-2 bits)
    """
    if temperature > 5.0:
        # Large jump: XOR with random 64-bit value
        return seed ^ rng.randint(0, 2**64 - 1)
    elif temperature > 1.0:
        # Medium: flip 8-16 bits
        n_bits = rng.randint(8, 16)
        mask = 0
        for _ in range(n_bits):
            mask |= 1 << rng.randint(0, 63)
        return seed ^ mask
    else:
        # Fine: flip 1-3 bits
        n_bits = rng.randint(1, 3)
        mask = 0
        for _ in range(n_bits):
            mask |= 1 << rng.randint(0, 63)
        return seed ^ mask


def hash_derived_seed(source: np.ndarray, target: np.ndarray) -> int:
    """Deterministic starting seed from source+target — same on encoder and decoder."""
    h = hashlib.sha256(source.tobytes() + target.tobytes()).digest()
    return int.from_bytes(h[:8], 'little')


# ---------------------------------------------------------------------------
# Main annealer
# ---------------------------------------------------------------------------

def anneal(
    source: np.ndarray,
    target: np.ndarray,
    n: int,
    max_k: int,
    n_iterations: int,
    initial_temp: float,
    cooling_rate: float,
    seed_master: int = 42,
    verbose: bool = True,
) -> dict:
    rng = random.Random(seed_master)

    # Start from hash-derived seed
    current_seed = hash_derived_seed(source, target)
    current_sigma = make_sigma(n, current_seed)
    current_k, current_mm, current_arr = best_k_for_sigma(source, target, current_sigma, max_k)

    best_seed = current_seed
    best_k = current_k
    best_mm = current_mm
    best_arr = current_arr.copy()

    temperature = initial_temp
    t0 = time.perf_counter()
    last_print = t0
    improvements = 0
    metropolis_accepts = 0

    if verbose:
        print(f"  Start: seed={current_seed:#018x}  mm={current_mm:,}  k={current_k}  T={temperature:.2f}")

    for iteration in range(n_iterations):
        if best_mm == 0:
            break

        # Mutate seed
        candidate_seed = mutate_seed(current_seed, rng, temperature)
        candidate_sigma = make_sigma(n, candidate_seed)
        candidate_k, candidate_mm, candidate_arr = best_k_for_sigma(
            source, target, candidate_sigma, max_k
        )

        # Accept/reject
        delta = candidate_mm - current_mm
        accepted = False
        if delta < 0:
            accepted = True
            improvements += 1
        elif temperature > 1e-12:
            prob = math.exp(-delta / temperature)
            if rng.random() < prob:
                accepted = True
                metropolis_accepts += 1

        if accepted:
            current_seed = candidate_seed
            current_mm = candidate_mm
            current_k = candidate_k
            current_arr = candidate_arr

        if candidate_mm < best_mm:
            best_seed = candidate_seed
            best_mm = candidate_mm
            best_k = candidate_k
            best_arr = candidate_arr.copy()

        temperature *= cooling_rate

        # Progress report
        now = time.perf_counter()
        if verbose and (now - last_print > 5.0 or best_mm == 0):
            elapsed = now - t0
            rate = (iteration + 1) / elapsed
            print(f"  iter={iteration+1:,}  best_mm={best_mm:,} ({100*best_mm/n:.1f}%)  "
                  f"k={best_k}  T={temperature:.4f}  "
                  f"impr={improvements}  metro={metropolis_accepts}  "
                  f"{rate:.0f} iter/s  {elapsed:.1f}s")
            last_print = now
            sys.stdout.flush()

    elapsed = time.perf_counter() - t0
    return {
        "best_seed": best_seed,
        "best_k": best_k,
        "best_mm": best_mm,
        "best_arr": best_arr,
        "iterations": min(n_iterations, iteration + 1),
        "improvements": improvements,
        "metropolis_accepts": metropolis_accepts,
        "elapsed": round(elapsed, 2),
    }


# ---------------------------------------------------------------------------
# Run
# ---------------------------------------------------------------------------

def run(raw: bytes, max_k: int, n_iterations: int, initial_temp: float,
        cooling_rate: float, seed_master: int = 42) -> dict:

    t0 = time.perf_counter()
    source_list, target_list, params, freq_l1 = materialise_source_and_target(raw)
    n = len(target_list)
    source = np.array(source_list, dtype=np.uint8)
    target = np.array(target_list, dtype=np.uint8)
    prep_time = time.perf_counter() - t0

    print(f"  n={n:,}  freq_L1={freq_l1:,}  prep={prep_time:.2f}s")
    print(f"  max_k={max_k}  n_iterations={n_iterations:,}  T0={initial_temp}  cooling={cooling_rate}")
    print()

    result = anneal(source, target, n, max_k, n_iterations, initial_temp, cooling_rate, seed_master)

    final_mm = result["best_mm"]
    final_k = result["best_k"]
    final_seed = result["best_seed"]

    # Recipe size
    seed_bits = 64
    k_bits = math.ceil(math.log2(max(final_k + 1, 2)))
    overhead_bits = 193  # K-coords + delta
    recipe_bits = seed_bits + k_bits
    total_bits = overhead_bits + recipe_bits
    file_bits = len(raw) * 8
    ratio = file_bits / total_bits if total_bits > 0 else 0

    # Hash verification if exact
    exact = final_mm == 0
    verify_hash = ""
    if exact:
        verify_hash = hashlib.sha256(result["best_arr"].tobytes()).hexdigest()[:16]

    print(f"\n  {'='*60}")
    print(f"  SUMMARY")
    print(f"  Iterations:     {result['iterations']:,}")
    print(f"  Improvements:   {result['improvements']:,}")
    print(f"  Metropolis:     {result['metropolis_accepts']:,}")
    print(f"  Time:           {result['elapsed']}s")
    print(f"  Best seed:      {final_seed:#018x}")
    print(f"  Best k:         {final_k}")
    print(f"  Final mismatch: {final_mm:,}  ({100*final_mm/n:.2f}% of digits)")
    print(f"  Recipe:         (seed={final_seed:#018x}, k={final_k})")
    print(f"  Recipe bits:    {recipe_bits} ({seed_bits} seed + {k_bits} k)")
    print(f"  Total w/ K:     {total_bits} bits = {total_bits//8} bytes")
    print(f"  File:           {len(raw):,} bytes")
    print(f"  Ratio:          {ratio:.1f}:1  {'(EXACT RECONSTRUCTION)' if exact else '(residual remains)'}")
    if exact:
        print(f"  Hash (first 16): {verify_hash}")

    return {
        "file_bytes": len(raw),
        "n_digits": n,
        "final_mismatch": final_mm,
        "best_seed": final_seed,
        "best_k": final_k,
        "recipe_bits": recipe_bits,
        "total_bits": total_bits,
        "ratio": round(ratio, 2),
        "exact": exact,
        "verify_hash": verify_hash,
        "iterations": result["iterations"],
        "elapsed": result["elapsed"],
    }


def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument("files", nargs="+")
    p.add_argument("--max-k", type=int, default=20,
                   help="Max sigma steps to try per seed (default 20)")
    p.add_argument("--iterations", type=int, default=10000,
                   help="Annealing iterations (default 10000)")
    p.add_argument("--temp", type=float, default=50.0,
                   help="Initial temperature (default 50.0)")
    p.add_argument("--cooling", type=float, default=0.9995,
                   help="Cooling rate per iteration (default 0.9995)")
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--json-out")
    return p.parse_args()


def main():
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V31 — SEED ANNEALER                                   ║")
    print("║  SA search over seed space → (seed, k) recipe              ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    all_results = []
    for f in args.files:
        path = Path(f).expanduser()
        print(f"\n{'='*72}")
        print(f"  File: {path.name}  ({path.stat().st_size:,} bytes)")
        print(f"{'='*72}")
        result = run(path.read_bytes(), args.max_k, args.iterations,
                     args.temp, args.cooling, args.seed)
        all_results.append(result)

    if args.json_out:
        import json
        # can't serialise numpy arrays directly
        for r in all_results:
            r.pop("best_arr", None)
        with open(args.json_out, "w") as fh:
            json.dump(all_results, fh, indent=2)
        print(f"\nResults written to {args.json_out}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
