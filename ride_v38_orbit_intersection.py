#!/usr/bin/env python3
"""
RIDE V38 - True orbit intersection: find single (seed, k) where sigma^k(source) == target.
# v1.0 — 2026-04-13 — correct model: ONE seed, ONE k, bit-perfect reconstruction

THE CORRECT MODEL
-----------------
The previous versions (v33-v37) were doing multi-stage greedy hill-climbing,
accepting a different (a,b) sigma at each stage. That requires transmitting
(a1,b1,k1), (a2,b2,k2), ... — a list. That's NOT the seed+k model.

THE TRUE SEED+K MODEL
---------------------
Sender finds ONE sigma (defined by seed S) such that:
    sigma^k(source) == target   for some k

Recipe = (S, k) — two numbers. Decoder:
1. Regenerate sigma = affine_sigma(a,b) where (a,b) = f(S)
2. Apply sigma k times to source
3. Verify hash matches — done, bit-perfect

THE SEARCH PROBLEM
------------------
For a given sigma (one (a,b) pair), the orbit of source is:
    source, sigma(source), sigma^2(source), ..., sigma^(ord-1)(source)

where ord = lcm of all cycle lengths in sigma (the permutation order).

The question is: does target appear on this orbit?

For exact reconstruction, we need sigma^k(source)[i] == target[i] for ALL i.

SEARCH STRATEGY
---------------
For each candidate (a,b) sigma:
1. Compute sigma's cycle structure
2. For each position i, find where source[i] ends up after k steps in the cycle containing i
3. We need: for every position i, after k steps in its cycle, source[i] == target[i]

This means: for each cycle (p0, p1, ..., p_{L-1}):
    source[p_j] must equal target[p_{(j+k) mod L}]
    for all j in the cycle

This is equivalent to: the cycle's source-values rotated by k must equal its target-values.
Each cycle independently constrains k mod L.

If all cycles agree on a single k (mod lcm), bit-perfect reconstruction is possible.

TARGET-AWARE SIGMA SCORING
---------------------------
Before doing full orbit search, score each (a,b) by:
  - For each cycle, check if source-values rotated by ANY shift match target-values
  - If a cycle has NO valid shift, this sigma can NEVER hit target — skip it
  - Count cycles with valid shifts — higher is better

This lets us prune impossible sigmas before expensive search.

RECIPE SIZE
-----------
Recipe = (a, b, k):
  - a: ceil(log2(n)) bits ≈ 12 bits
  - b: ceil(log2(n)) bits ≈ 12 bits
  - k: ceil(log2(max_k)) bits ≈ varies
  - Total: ~30-40 bits per stage IF this works

But the goal is ONE (a,b,k) that achieves sigma^k(source) == target.
If that's possible: recipe ≈ 36 bits = 4.5 bytes for n=2293.
File = 952 bytes → ratio = 952/4.5 ≈ 211:1

REALISTIC EXPECTATION
---------------------
A random affine sigma has orbit structure that almost certainly doesn't
pass through an arbitrary target. The question is whether target-informed
search can find one that does — or how close we can get in one shot.

This version:
1. For each candidate sigma, finds the best k (minimizing mile to target)
2. Reports the BEST single (a,b,k) triple found across all candidates
3. Shows if any sigma achieves mile=0 (exact reconstruction)
4. If not, reports the minimum mile achievable with a single sigma application

This is the correct single-shot model: sender finds best (a,b,k), transmits it,
decoder applies once, done (or as close to done as possible).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
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

import numpy as np

from ride_v18_cycle_rsn import materialise_source_and_target
from ride_v24_order_family_harness import (
    K_CANDIDATES,
    ResidualStats,
    affine_sigma,
    apply_perm_power,
    better,
    coprime_multiplier,
    decompose_perm,
    residual_stats,
    stats_key,
)
from ride_v16_whole_file_orbit_steps import PCG32


# ---------------------------------------------------------------------------
# Cycle-level orbit analysis
# ---------------------------------------------------------------------------

def cycle_valid_shifts(source: list[int], target: list[int],
                       cycle: list[int]) -> list[int]:
    """
    For a cycle (p0, p1, ..., p_{L-1}), find all shifts k (0 <= k < L) such that:
        source[p_j] == target[p_{(j+k) % L}]  for all j in 0..L-1

    A valid shift k means: after k applications of sigma, every position in this
    cycle has the right value from source ending up at the right target position.

    Returns list of valid shifts (may be empty if no shift works).
    """
    L = len(cycle)
    if L == 1:
        # Fixed point: source[cycle[0]] must equal target[cycle[0]]
        if source[cycle[0]] == target[cycle[0]]:
            return [0]
        else:
            return []  # This cycle can never be satisfied

    src_vals = [source[p] for p in cycle]
    tgt_vals = [target[p] for p in cycle]

    # Find shifts k where rotating src_vals by k matches tgt_vals
    # src_vals rotated by k: src_vals[k], src_vals[k+1], ..., src_vals[k+L-1] (mod L)
    # Wait: sigma^k moves position p_j to p_{j+k mod L}
    # So after k steps: new[p_{j+k mod L}] = old[p_j] = source[p_j]
    # We want new[p_i] = target[p_i] for all i
    # new[p_i] = source[p_{i-k mod L}]
    # So: source[p_{i-k mod L}] == target[p_i] for all i
    # Equivalently: src_vals[(i-k) mod L] == tgt_vals[i] for all i
    # Or: tgt_vals[(j+k) mod L] == src_vals[j] for all j  (substitute j=i-k)

    valid = []
    for k in range(L):
        match = all(tgt_vals[(j + k) % L] == src_vals[j] for j in range(L))
        if match:
            valid.append(k)
    return valid


def find_exact_k(source: list[int], target: list[int],
                 cycles: list[list[int]]) -> int | None:
    """
    Given sigma's cycles, find k such that sigma^k(source) == target, or None.

    For each cycle, find valid shifts. Then use CRT to find k satisfying all constraints.
    """
    # For each cycle, get valid shifts mod cycle_length
    constraints = []  # (valid_shifts, cycle_length) per cycle
    for cycle in cycles:
        valid = cycle_valid_shifts(source, target, cycle)
        if not valid:
            return None  # This sigma can never hit target
        constraints.append((valid, len(cycle)))

    # Try to find k satisfying all constraints via CRT
    # For cycles with multiple valid shifts, try all combinations (exponential in worst case)
    # But in practice most cycles have 0 or 1 valid shifts
    # Start with k=0 candidate, build up via CRT
    # Simple approach: try k from 0 to lcm of all cycle lengths

    # Compute lcm of all cycle lengths
    from math import gcd
    cycle_lengths = [len(c) for c in cycles]
    order = 1
    for L in cycle_lengths:
        order = order * L // gcd(order, L)

    # Cap search: if order is huge, just try up to MAX_K
    MAX_K = min(order, 100_000)

    # For efficiency, precompute constraint sets
    constraint_sets = []
    for cycle in cycles:
        valid = cycle_valid_shifts(source, target, cycle)
        if not valid:
            return None
        L = len(cycle)
        # Expand to set of valid k mod L
        constraint_sets.append((set(valid), L))

    # Find k in [0, MAX_K) satisfying all constraints
    for k in range(MAX_K):
        if all(k % L in vset for vset, L in constraint_sets):
            return k

    return None


# ---------------------------------------------------------------------------
# Single-shot orbit search: find best (a,b,k) globally
# ---------------------------------------------------------------------------

def orbit_intersection_search(
    source: list[int],
    target: list[int],
    n: int,
    n_candidates: int,
    rng: random.Random,
    verbose: bool = False,
) -> tuple[list[int] | None, ResidualStats | None, dict, int | None]:
    """
    Search for (a,b,k) such that affine_sigma(a,b)^k(source) is as close to target as possible.

    Returns: (best_state, best_stats, best_meta, exact_k)
    exact_k is non-None if sigma^k(source) == target exactly.
    """
    source_stats = residual_stats(source, target)
    best_state = None
    best_stats = source_stats
    best_meta = {}
    exact_k = None

    n_exact = 0
    n_checked = 0

    for i in range(n_candidates):
        a = rng.randint(2, n - 1)
        while math.gcd(a, n) != 1:
            a = (a + 1) % n
            if a < 2:
                a = 2
        b = rng.randint(0, n - 1)

        sigma = affine_sigma(n, a, b)
        cycles = decompose_perm(sigma)

        # Try to find exact k first (fast CRT approach)
        k_exact = find_exact_k(source, target, cycles)
        n_checked += 1

        if k_exact is not None:
            # Found exact reconstruction!
            state = apply_perm_power(source, sigma, cycles, k_exact)
            stats = residual_stats(state, target)
            if stats.mile == 0:
                n_exact += 1
                exact_k = k_exact
                best_state = state
                best_stats = stats
                best_meta = {"a": a, "b": b, "k": k_exact, "exact": True}
                print(f"  *** EXACT K FOUND: a={a}, b={b}, k={k_exact} at candidate {i+1} ***")
                break
            # Even if CRT says valid, verify (might be off due to fixed-point interactions)

        # Also do standard k-search for best approximate result
        cycle_lengths = sorted((len(c) for c in cycles), reverse=True)[:4]
        k_values = sorted(
            set(K_CANDIDATES)
            | {v for l in cycle_lengths
               for v in (l // 4, l // 2, (3 * l) // 4, l - 1)
               if 0 < v}
        )

        for k in k_values[:20]:
            if k == 0:
                continue
            candidate = apply_perm_power(source, sigma, cycles, k)
            cstats = residual_stats(candidate, target)
            if better(cstats, best_stats):
                best_state = candidate
                best_stats = cstats
                best_meta = {"a": a, "b": b, "k": k, "exact": False}

        if verbose and (i + 1) % 1000 == 0:
            print(f"    Checked {i+1}/{n_candidates}, best mile={best_stats.mile:,}, exact={n_exact}")

    return best_state, best_stats, best_meta, exact_k


# ---------------------------------------------------------------------------
# Target-informed pre-scoring (from v37) + exact orbit check
# ---------------------------------------------------------------------------

def score_affine_np(source_np: np.ndarray, target_np: np.ndarray,
                    a: int, b: int, n: int) -> int:
    """Score how many positions sigma moves to the right value."""
    indices = np.arange(n, dtype=np.int64)
    src_indices = (a * indices + b) % n
    moved_target = target_np[src_indices]
    return int(np.sum(source_np == moved_target))


def targeted_orbit_search(
    source: list[int],
    target: list[int],
    n: int,
    n_score: int,
    n_search: int,
    rng: random.Random,
) -> tuple[list[int] | None, ResidualStats | None, dict, int | None]:
    """
    Phase 1: Score n_score (a,b) pairs by target alignment.
    Phase 2: On top n_search, try full orbit intersection (exact k search + k-search).
    """
    source_np = np.array(source, dtype=np.uint8)
    target_np = np.array(target, dtype=np.uint8)
    source_stats = residual_stats(source, target)

    # Phase 1: cheap scoring
    scored = []
    for _ in range(n_score):
        a = rng.randint(2, n - 1)
        while math.gcd(a, n) != 1:
            a = (a + 1) % n
            if a < 2:
                a = 2
        b = rng.randint(0, n - 1)
        sc = score_affine_np(source_np, target_np, a, b, n)
        scored.append((sc, a, b))

    scored.sort(reverse=True)
    top = scored[:n_search]

    best_state = None
    best_stats = source_stats
    best_meta = {}
    exact_k = None

    for score, a, b in top:
        sigma = affine_sigma(n, a, b)
        cycles = decompose_perm(sigma)

        # Try exact orbit intersection
        k_exact = find_exact_k(source, target, cycles)
        if k_exact is not None:
            state = apply_perm_power(source, sigma, cycles, k_exact)
            stats = residual_stats(state, target)
            if stats.mile == 0:
                exact_k = k_exact
                best_state = state
                best_stats = stats
                best_meta = {"a": a, "b": b, "k": k_exact, "exact": True, "pre_score": score}
                print(f"  *** EXACT RECONSTRUCTION: a={a}, b={b}, k={k_exact} ***")
                return best_state, best_stats, best_meta, exact_k

        # Standard k-search
        cycle_lengths = sorted((len(c) for c in cycles), reverse=True)[:4]
        k_values = sorted(
            set(K_CANDIDATES)
            | {v for l in cycle_lengths
               for v in (l // 4, l // 2, (3 * l) // 4, l - 1)
               if 0 < v}
        )

        for k in k_values[:20]:
            if k == 0:
                continue
            candidate = apply_perm_power(source, sigma, cycles, k)
            cstats = residual_stats(candidate, target)
            if better(cstats, best_stats):
                best_state = candidate
                best_stats = cstats
                best_meta = {"a": a, "b": b, "k": k, "exact": False, "pre_score": score}

    return best_state, best_stats, best_meta, exact_k


# ---------------------------------------------------------------------------
# Runner: report what a single best (a,b,k) achieves
# ---------------------------------------------------------------------------

def run(raw: bytes, n_score: int, n_search: int, n_random: int, seed: int = 42) -> dict:
    t0 = time.perf_counter()
    source_digits, target_digits, params, l1 = materialise_source_and_target(raw)
    n = len(target_digits)
    source = list(source_digits)
    target = list(target_digits)
    prep_time = time.perf_counter() - t0

    print(f"  n={n:,}  freq_L1={l1:,}  prep={prep_time:.2f}s")
    print(f"  n_score={n_score:,}  n_search={n_search}  n_random={n_random:,}")

    init_stats = residual_stats(source, target)
    init_mt = sum(1 for i in range(n) if source[i] != target[i])
    print(f"  Initial mile={init_stats.mile:,}  mismatch={init_mt:,}")
    print()

    rng = random.Random(seed)

    # -----------------------------------------------------------------------
    # Approach 1: Target-informed scoring + exact orbit check
    # -----------------------------------------------------------------------
    print(f"  [Approach 1] Target-informed: score {n_score:,} pairs, orbit-check top {n_search}")
    t1 = time.perf_counter()
    state1, stats1, meta1, ek1 = targeted_orbit_search(
        source, target, n, n_score, n_search, rng
    )
    t1 = time.perf_counter() - t1

    if stats1 is not None:
        a1, b1, k1 = meta1.get("a", 0), meta1.get("b", 0), meta1.get("k", 0)
        pos_bits = math.ceil(math.log2(max(n, 2)))
        k_bits = math.ceil(math.log2(max(k1 + 1, 2)))
        recipe_bits = pos_bits + pos_bits + k_bits
        mile_drop = init_stats.mile - stats1.mile
        pct = 100 * mile_drop / init_stats.mile if init_stats.mile > 0 else 0
        print(f"  Best single (a,b,k): a={a1}, b={b1}, k={k1}")
        print(f"  Mile: {init_stats.mile:,} → {stats1.mile:,}  (drop={mile_drop:,}, {pct:.1f}%)")
        print(f"  Exact reconstruction: {ek1 is not None}")
        print(f"  Recipe bits: {recipe_bits} ({recipe_bits//8} bytes + {recipe_bits%8} bits)")
        print(f"  Time: {t1:.1f}s")
        print()
    else:
        print(f"  No improvement found.")
        print()

    # -----------------------------------------------------------------------
    # Approach 2: Pure random orbit search with exact-k check
    # -----------------------------------------------------------------------
    print(f"  [Approach 2] Pure random orbit search: {n_random:,} candidates")
    t2 = time.perf_counter()
    state2, stats2, meta2, ek2 = orbit_intersection_search(
        source, target, n, n_random, rng, verbose=True
    )
    t2 = time.perf_counter() - t2

    if stats2 is not None:
        a2, b2, k2 = meta2.get("a", 0), meta2.get("b", 0), meta2.get("k", 0)
        pos_bits = math.ceil(math.log2(max(n, 2)))
        k_bits = math.ceil(math.log2(max(k2 + 1, 2)))
        recipe_bits = pos_bits + pos_bits + k_bits
        mile_drop = init_stats.mile - stats2.mile
        pct = 100 * mile_drop / init_stats.mile if init_stats.mile > 0 else 0
        print(f"  Best single (a,b,k): a={a2}, b={b2}, k={k2}")
        print(f"  Mile: {init_stats.mile:,} → {stats2.mile:,}  (drop={mile_drop:,}, {pct:.1f}%)")
        print(f"  Exact reconstruction: {ek2 is not None}")
        print(f"  Recipe bits: {recipe_bits} ({recipe_bits//8} bytes + {recipe_bits%8} bits)")
        print(f"  Time: {t2:.1f}s")
    else:
        print(f"  No improvement found.")

    # -----------------------------------------------------------------------
    # Summary: what does the BEST single sigma achieve?
    # -----------------------------------------------------------------------
    print()
    print(f"  {'='*60}")
    print(f"  SINGLE SIGMA SUMMARY")

    best_overall = stats1
    best_meta_overall = meta1
    ek_overall = ek1
    if stats2 is not None and (best_overall is None or better(stats2, best_overall)):
        best_overall = stats2
        best_meta_overall = meta2
        ek_overall = ek2

    if best_overall is not None:
        pos_bits = math.ceil(math.log2(max(n, 2)))
        k_final = best_meta_overall.get("k", 0)
        k_bits = math.ceil(math.log2(max(k_final + 1, 2)))
        recipe_bits = pos_bits + pos_bits + k_bits
        overhead_bits = 193
        total_bits = overhead_bits + recipe_bits
        file_bits = len(raw) * 8
        ratio = file_bits / total_bits

        print(f"  Best (a,b,k): a={best_meta_overall.get('a')}, b={best_meta_overall.get('b')}, k={k_final}")
        print(f"  Mile after: {best_overall.mile:,} / {init_stats.mile:,}")
        print(f"  Exact reconstruction: {ek_overall is not None}")
        print(f"  Recipe: {recipe_bits} bits = {recipe_bits//8} bytes")
        print(f"  Total (with K-overhead): {total_bits} bits = {total_bits//8} bytes")
        print(f"  File: {len(raw):,} bytes = {file_bits} bits")
        print(f"  Ratio: {ratio:.1f}:1")

        if best_overall.mile > 0:
            print()
            print(f"  NOTE: Single sigma does NOT achieve exact reconstruction.")
            print(f"  Remaining mile={best_overall.mile:,} requires additional work.")
            print(f"  Multi-stage is needed, OR a different sigma family.")

    return {
        "file_bytes": len(raw),
        "n_digits": n,
        "init_mile": init_stats.mile,
        "best_mile": best_overall.mile if best_overall else init_stats.mile,
        "exact": ek_overall is not None,
        "recipe_bits": recipe_bits if best_overall else 0,
    }


def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument("files", nargs="+")
    p.add_argument("--n-score", type=int, default=100_000,
                   help="(a,b) pairs to score cheaply (default 100000)")
    p.add_argument("--n-search", type=int, default=100,
                   help="Top pairs to do orbit intersection check on (default 100)")
    p.add_argument("--n-random", type=int, default=5000,
                   help="Additional random candidates for orbit search (default 5000)")
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--json-out")
    return p.parse_args()


def main():
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V38 — TRUE ORBIT INTERSECTION SEARCH                 ║")
    print("║  Find single (a,b,k): sigma^k(source) == target            ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    all_results = []
    for f in args.files:
        path = Path(f).expanduser()
        print(f"\n{'='*72}")
        print(f"  File: {path.name}  ({path.stat().st_size:,} bytes)")
        print(f"{'='*72}")
        result = run(path.read_bytes(), args.n_score, args.n_search,
                     args.n_random, args.seed)
        all_results.append(result)

    if args.json_out:
        with open(args.json_out, "w") as fh:
            json.dump(all_results, fh, indent=2)
        print(f"\nResults written to {args.json_out}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
