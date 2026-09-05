#!/usr/bin/env python3
"""
RIDE V37 - Target-informed affine search: encoder uses both files to guide (a,b) selection.
# v1.0 — 2026-04-13 — encoder scores affine candidates by target alignment before k search

THE KEY INSIGHT
---------------
The encoder has BOTH source and target. At each stage it knows:
  - current state C (both sides have this)
  - target T (encoder only — but that's fine, sender does the search)
  - wrong positions: M_T = {i : C[i] != T[i]}
  - for each wrong position i: need T[i] at position i, currently have C[i]

Instead of random (a,b) pairs, the encoder generates (a,b) and SCORES them
before the expensive k-search:

Score(a,b) = |{i in M_T : C[affine(i)] == T[i]}|
           = number of positions that will get the RIGHT value after one affine step

High-score (a,b) pairs are far more likely to reduce mile when applied as sigma^k.
We can evaluate the score in O(n) per (a,b) candidate, then only do the full
k-search on the top-scoring candidates.

This lets us:
1. Generate 100,000 random (a,b) pairs cheaply (just score, no k-search)
2. Keep top 100 by score
3. Do full k-search only on those 100

Total cost: 100,000 × O(n) scoring + 100 × K × O(n) k-search
vs current:  5,000 × K × O(n) k-search

But more importantly: the top-scoring (a,b) pairs are STRUCTURALLY aligned
with the actual displacement map, not random. This is how the TSP engine
uses both files to guide search.

DECODER REPRODUCIBILITY
-----------------------
The decoder gets (a,b,k). It applies the global affine sigma to current state.
Same result as encoder. The scoring is encoder-only search overhead — not transmitted.
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
# Fast numpy scoring of affine candidate
# ---------------------------------------------------------------------------

def score_affine(current_np: np.ndarray, target_np: np.ndarray,
                 a: int, b: int, n: int) -> int:
    """
    Count positions i where current[affine(i)] == target[i].
    affine(i) = (a*i + b) % n.
    This is O(n) via numpy — fast enough to score 100k candidates.
    """
    indices = np.arange(n, dtype=np.int64)
    src_indices = (a * indices + b) % n
    # After applying sigma: new[i] = current[sigma^{-1}(i)]
    # sigma(j) = i means j goes to position i
    # Actually: apply_sigma means result[sigma(i)] = current[i]
    # So result[i] = current[sigma^{-1}(i)]
    # sigma(j) = (a*j+b)%n, so sigma^{-1}(i) = (a_inv*(i-b))%n
    # Score: how many i have result[i] == target[i]
    # = how many i have current[sigma^{-1}(i)] == target[i]
    # = how many j=sigma^{-1}(i) have current[j] == target[sigma(j)]
    # = how many j have current[j] == target[(a*j+b)%n]
    moved_target = target_np[src_indices]  # target[(a*j+b)%n] for each j
    return int(np.sum(current_np == moved_target))


# ---------------------------------------------------------------------------
# Targeted affine candidates: score first, k-search second
# ---------------------------------------------------------------------------

def targeted_affine_candidates(
    current: list[int],
    target: list[int],
    current_stats: ResidualStats,
    n: int,
    n_score: int,       # how many (a,b) pairs to score
    n_search: int,      # how many top-scoring to do k-search on
    top_ks: int,
    rng: random.Random,
) -> list[tuple[list[int], ResidualStats, dict[str, Any]]]:

    current_np = np.array(current, dtype=np.uint8)
    target_np = np.array(target, dtype=np.uint8)

    # Phase 1: score n_score random (a,b) pairs
    scored = []
    for _ in range(n_score):
        a = rng.randint(2, n - 1)
        if math.gcd(a, n) != 1:
            # Make coprime by simple adjustment
            while a < n and math.gcd(a, n) != 1:
                a += 1
            if a >= n:
                a = 1
        b = rng.randint(0, n - 1)
        score = score_affine(current_np, target_np, a, b, n)
        scored.append((score, a, b))

    # Keep top n_search by score
    scored.sort(reverse=True)
    top = scored[:n_search]

    # Phase 2: full k-search on top candidates
    candidates = []
    for score, a, b in top:
        sigma = affine_sigma(n, a, b)
        cycles = decompose_perm(sigma)
        cycle_lengths = sorted((len(c) for c in cycles), reverse=True)[:4]
        k_values = sorted(
            set(K_CANDIDATES)
            | {v for l in cycle_lengths
               for v in (l // 4, l // 2, (3 * l) // 4, l - 1)
               if 0 < v}
        )

        for k in k_values[:top_ks]:
            if k == 0:
                continue
            candidate = apply_perm_power(current, sigma, cycles, k)
            cstats = residual_stats(candidate, target)
            meta = {
                "family": "targeted_affine",
                "a": a, "b": b, "k": k,
                "pre_score": score,
            }
            candidates.append((candidate, cstats, meta))

    candidates.sort(key=lambda item: stats_key(item[1]))
    return candidates


# ---------------------------------------------------------------------------
# Multi-stage runner
# ---------------------------------------------------------------------------

def run(raw: bytes, n_stages: int, n_score: int, n_search: int,
        top_ks: int, master_seed: int = 42) -> dict:

    t0 = time.perf_counter()
    source_digits, target_digits, params, l1 = materialise_source_and_target(raw)
    n = len(target_digits)
    source = list(source_digits)
    target = list(target_digits)
    prep_time = time.perf_counter() - t0

    print(f"  n={n:,}  freq_L1={l1:,}  prep={prep_time:.2f}s")
    print(f"  n_score={n_score:,}  n_search={n_search}  top_ks={top_ks}  stages={n_stages}")
    print()
    print(f"  {'Stage':>5}  {'Mile':>7}  {'M_T':>6}  {'Score':>6}  "
          f"{'a':>6}  {'b':>6}  {'k':>4}  {'Bits':>5}  {'bpm':>6}  {'Time':>5}")
    print(f"  {'-'*5}  {'-'*7}  {'-'*6}  {'-'*6}  {'-'*6}  {'-'*6}  {'-'*4}  {'-'*5}  {'-'*6}  {'-'*5}")

    current = list(source_digits)
    init_stats = residual_stats(current, target)
    init_mt = sum(1 for i in range(n) if current[i] != target[i])
    print(f"  {'init':>5}  {init_stats.mile:>7,}  {init_mt:>6,}")

    rng = random.Random(master_seed)
    stage_results = []
    total_recipe_bits = 0
    pos_bits = math.ceil(math.log2(max(n, 2)))
    prev_mile = init_stats.mile
    stall_count = 0

    for stage_idx in range(1, n_stages + 1):
        t_stage = time.perf_counter()
        current_stats = residual_stats(current, target)

        if current_stats.mile == 0:
            print(f"\n  *** EXACT RECONSTRUCTION at stage {stage_idx}! ***")
            verify = hashlib.sha256(bytes(current)).hexdigest()[:16]
            tgt_h  = hashlib.sha256(bytes(target)).hexdigest()[:16]
            print(f"  Result hash: {verify}  Target: {tgt_h}  Match: {verify==tgt_h}")
            break

        candidates = targeted_affine_candidates(
            current, target, current_stats, n,
            n_score, n_search, top_ks, rng
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

        a = best_meta.get("a", 0)
        b = best_meta.get("b", 0)
        k = best_meta.get("k", 0)
        pre_score = best_meta.get("pre_score", 0)

        mile_drop = prev_mile - best_stats.mile
        stage_bits = 0
        bpm = float('inf')
        if improved:
            stage_bits = pos_bits + pos_bits + math.ceil(math.log2(max(k + 1, 2)))
            bpm = stage_bits / mile_drop if mile_drop > 0 else float('inf')
        total_recipe_bits += stage_bits
        prev_mile = best_stats.mile

        mt = sum(1 for i in range(n) if current[i] != target[i])
        marker = "***" if improved else "   "
        print(f"  {stage_idx:>5}  {best_stats.mile:>7,}  {mt:>6,}  {pre_score:>6,}  "
              f"{a:>6}  {b:>6}  {k:>4}  {stage_bits:>5}  "
              f"{bpm:>6.2f}  {stage_time:>4.1f}s  {marker}")
        sys.stdout.flush()

        stage_results.append({
            "stage": stage_idx,
            "improved": improved,
            "mile": best_stats.mile,
            "m_t": mt,
            "pre_score": pre_score,
            "a": a, "b": b, "k": k,
            "recipe_bits": stage_bits,
            "bpm": round(bpm, 3) if bpm < 1e9 else None,
        })

        if not improved:
            stall_count += 1
            if stall_count >= 3:
                print(f"\n  Stalled for 3 consecutive stages.")
                break
        else:
            stall_count = 0

    final_stats = residual_stats(current, target)
    file_bits = len(raw) * 8
    overhead_bits = 193
    total_bits = overhead_bits + total_recipe_bits
    ratio = file_bits / total_bits if total_bits > 0 else 0
    total_drop = init_stats.mile - final_stats.mile
    avg_bpm = total_recipe_bits / total_drop if total_drop > 0 else float('inf')

    print(f"\n  {'='*60}")
    print(f"  SUMMARY")
    print(f"  Stages:         {len(stage_results)}")
    print(f"  Mile:           {init_stats.mile:,} → {final_stats.mile:,}  (drop={total_drop:,})")
    print(f"  Avg bits/mile:  {avg_bpm:.3f}")
    print(f"  Recipe bits:    {total_recipe_bits} = {total_recipe_bits//8} bytes")
    print(f"  Total w/ K:     {total_bits} bits = {total_bits//8} bytes")
    print(f"  File:           {len(raw):,} bytes")
    print(f"  Ratio:          {ratio:.1f}:1")
    if final_stats.mile > 0 and avg_bpm < 1e9:
        proj_order_bits = int(final_stats.mile * avg_bpm)
        proj_total = total_bits + proj_order_bits
        print(f"  Projected to 0: total {proj_total} bits = {proj_total//8} bytes")
        print(f"  Projected ratio: {file_bits/proj_total:.1f}:1")

    return {
        "file_bytes": len(raw),
        "n_digits": n,
        "init_mile": init_stats.mile,
        "final_mile": final_stats.mile,
        "total_recipe_bits": total_recipe_bits,
        "avg_bpm": round(avg_bpm, 3) if avg_bpm < 1e9 else None,
        "total_bits": total_bits,
        "ratio": round(ratio, 2),
        "stages": stage_results,
    }


def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument("files", nargs="+")
    p.add_argument("--stages", type=int, default=50)
    p.add_argument("--n-score", type=int, default=50000,
                   help="(a,b) pairs to score cheaply per stage (default 50000)")
    p.add_argument("--n-search", type=int, default=50,
                   help="Top-scored pairs to do full k-search on (default 50)")
    p.add_argument("--top-ks", type=int, default=20)
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--json-out")
    return p.parse_args()


def main():
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V37 — TARGET-INFORMED AFFINE SEARCH                  ║")
    print("║  Score 50k pairs cheap, k-search top 50 — encoder has both ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    all_results = []
    for f in args.files:
        path = Path(f).expanduser()
        print(f"\n{'='*72}")
        print(f"  File: {path.name}  ({path.stat().st_size:,} bytes)")
        print(f"{'='*72}")
        result = run(path.read_bytes(), args.stages, args.n_score,
                     args.n_search, args.top_ks, args.seed)
        all_results.append(result)

    if args.json_out:
        with open(args.json_out, "w") as fh:
            json.dump(all_results, fh, indent=2)
        print(f"\nResults written to {args.json_out}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
