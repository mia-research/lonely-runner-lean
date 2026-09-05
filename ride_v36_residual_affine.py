#!/usr/bin/env python3
"""
RIDE V36 - Residual-restricted affine: sigma acts only on wrong positions.
# v1.0 — 2026-04-13 — fresh affine on residual subspace each stage

THE KEY INSIGHT
---------------
After stage 1, ~2000 positions are still wrong. Applying a global affine
to all 2293 positions moves correct positions too, risking breaking them.
Worse, the affine has to "accidentally" get all 2293 positions right, not
just the 2000 wrong ones — an astronomically harder problem.

FIX: restrict sigma to only the mismatch positions.
  - Compute mismatch set M = {i : current[i] != source[i]}
  - Both encoder and decoder can compute M identically (they share current state + source)
  - Build affine sigma on indices 0..|M|-1, then map back to actual positions
  - This is an affine permutation of |M| elements, not n elements
  - After applying: positions in M are rearranged; positions not in M unchanged

WHY THIS HELPS
--------------
Stage 1: |M| ≈ 2056, sigma is affine on 2056 elements
Stage 2: |M| ≈ 1966 (after stage 1 fixed 90 positions)
...
Each stage: the sub-permutation is exactly the right size for the residual problem.
The affine family explores arrangements of the mismatch set, not the full array.
Mile reduction per stage should be similar to stage 1 (same search budget,
same fraction of space covered), not zero.

DECODER REPRODUCIBILITY
-----------------------
Decoder state at each stage = identical to encoder state (same accepted moves applied).
M is computable from current state + source (K-source, shared).
(a, b, k) are the only transmitted parameters per stage.

WAIT — decoder doesn't know SOURCE, it's building toward it.
Actually: decoder HAS source (K-source). The target is what it's building toward.
M = positions where current[i] != TARGET[i].
But decoder doesn't have target...

REVISED: M = positions where current[i] != source[i].
Since source = K-source (fully known to decoder), this is computable.
This is an approximation — it uses source-mismatch not target-mismatch.
At the start: current = source, so M = empty. After freq patch: M = freq patch positions.
After order moves: M tracks the positions that have been moved from source.

Hmm — but the GOAL is to reach target, not source. The decoder needs target-mismatch.

SOLUTION: use the source-sorted ordering.
Source = K-source = sorted arrangement (approximately).
Both sides know source. The mismatch vs source IS the disorder to be resolved.
The decoder's goal is to apply moves that converge source→target.
At each stage: M = {i : current[i] != source[i]} is the set of positions
that have been displaced from the K-source. But wait — we START at source
and want to reach target. The displacement is source[i] vs target[i].

OK let me think about this cleanly:
- Encoder starts with source S, wants to reach target T
- Current state C starts at S, moves toward T via accepted swaps
- After k stages: C is somewhere between S and T
- Mismatch set vs target: M_T = {i : C[i] != T[i]} — these are the remaining wrong positions
- Both encoder AND decoder know C at this point (same moves applied)
- But decoder doesn't know T... except it does — T IS the file being reconstructed

Actually: at decode time, the decoder is applying moves to S to build T.
It doesn't have T in advance — that's what it's computing.
So it CANNOT compute M_T without T.

BUT: the encoder can compute M_T (it has both C and T).
The encoder restricts sigma to M_T, finds good (a,b,k), transmits them.
The decoder applies the same (a,b,k) restricted to... what positions?

If the decoder applies (a,b,k) as a global affine (not restricted), it gets a
different result. The restriction must be reproducible.

REPRODUCIBLE RESTRICTION: use M_S = {i : C[i] != S[i]} (source mismatch).
Both sides can compute this — decoder has S and C.
The encoder searches over sigmas restricted to M_S.
This is an approximation: M_S ≠ M_T in general (some positions may have
the right value from a different source position, or vice versa).
But M_S is a reasonable proxy and is fully reproducible.

ALTERNATIVELY: transmit |M_T| as part of the recipe, and use M_T sorted order.
No — that requires transmitting M_T which is large.

PRAGMATIC SOLUTION: use M_S (source-mismatch). Both sides compute it identically.
The sigma acts on the ordered list of M_S positions. Recipe: (a, b, k).
This is fully decoder-reproducible and focuses search on displaced positions.
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
    stats_key,
)


# ---------------------------------------------------------------------------
# State seed from current state (decoder-reproducible)
# ---------------------------------------------------------------------------

def state_seed(state: list[int]) -> int:
    digest = hashlib.sha256(bytes(state)).digest()
    return int.from_bytes(digest[:8], 'little')


# ---------------------------------------------------------------------------
# Residual-restricted affine candidates
# ---------------------------------------------------------------------------

def residual_affine_candidates(
    current: list[int],
    source: list[int],
    target: list[int],
    n: int,
    n_affine: int,
    top_ks: int,
) -> list[tuple[list[int], ResidualStats, dict[str, Any]]]:
    """
    Generate affine sigmas restricted to the source-mismatch positions.
    M_S = sorted list of positions where current[i] != source[i].
    Affine sigma acts on indices 0..|M_S|-1, mapped to actual M_S positions.
    """
    # Compute M_S: positions displaced from source
    M_S = [i for i in range(n) if current[i] != source[i]]
    m = len(M_S)

    if m <= 1:
        return []

    seed = state_seed(current)
    rng = PCG32(seed)
    candidates = []

    for _ in range(n_affine):
        if m <= 2:
            a, b = 1, 1
        else:
            a = coprime_multiplier(rng, m)
            b = rng.next_uniform(m)

        # Build sub-permutation: sigma on [0..m-1] via affine
        sub_sigma = affine_sigma(m, a, b)
        sub_cycles = decompose_perm(sub_sigma)

        # k values to try
        cycle_lengths = sorted((len(c) for c in sub_cycles), reverse=True)[:4]
        k_values = sorted(
            set(K_CANDIDATES)
            | {v for l in cycle_lengths
               for v in (l // 4, l // 2, (3 * l) // 4, l - 1)
               if 0 < v}
        )

        for k in k_values[:top_ks]:
            if k == 0:
                continue

            # Apply sub-sigma^k: compute new positions of M_S elements
            sub_k = apply_perm_power(list(range(m)), sub_sigma, sub_cycles, k)

            # Build full candidate: rearrange M_S elements according to sub_k
            candidate = list(current)
            vals = [current[M_S[i]] for i in range(m)]
            for i in range(m):
                candidate[M_S[i]] = vals[sub_k[i]]

            cstats = residual_stats(candidate, target)
            meta = {
                "family": "residual_affine",
                "m": m,
                "a": a,
                "b": b,
                "k": k,
                "state_seed": seed,
            }
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
    source = list(source_digits)
    prep_time = time.perf_counter() - t0

    print(f"  n={n:,}  freq_L1={l1:,}  prep={prep_time:.2f}s")
    print(f"  n_affine={n_affine}  top_ks={top_ks}  stages={n_stages}")
    print()
    print(f"  {'Stage':>5}  {'Mile':>7}  {'|M_S|':>6}  {'|M_T|':>6}  "
          f"{'a':>6}  {'b':>6}  {'k':>4}  {'Bits':>5}  {'bpm':>6}  {'Time':>5}")
    print(f"  {'-----':>5}  {'-------':>7}  {'------':>6}  {'------':>6}  "
          f"{'------':>6}  {'------':>6}  {'----':>4}  {'-----':>5}  {'------':>6}  {'-----':>5}")

    current = list(source_digits)
    init_stats = residual_stats(current, target_digits)
    init_ms = sum(1 for i in range(n) if current[i] != source[i])
    print(f"  {'init':>5}  {init_stats.mile:>7,}  {init_ms:>6,}  {init_stats.mismatch:>6,}")

    stage_results = []
    total_recipe_bits = 0
    pos_bits = math.ceil(math.log2(max(n, 2)))
    prev_mile = init_stats.mile

    for stage_idx in range(1, n_stages + 1):
        t_stage = time.perf_counter()
        current_stats = residual_stats(current, target_digits)
        if current_stats.mile == 0:
            print(f"\n  *** Exact reconstruction at stage {stage_idx}! ***")
            break

        M_S = [i for i in range(n) if current[i] != source[i]]
        m = len(M_S)

        candidates = residual_affine_candidates(
            current, source, target_digits, n, n_affine, top_ks
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

        # Recipe: (a, b, k) — a,b are indices into [0..m-1], k is step count
        m_bits = math.ceil(math.log2(max(m, 2)))
        stage_bits = m_bits + m_bits + math.ceil(math.log2(max(k + 1, 2))) if improved else 0
        total_recipe_bits += stage_bits

        mile_drop = prev_mile - best_stats.mile
        bpm = stage_bits / mile_drop if mile_drop > 0 else float('inf')
        prev_mile = best_stats.mile

        M_T = sum(1 for i in range(n) if current[i] != target_digits[i])

        marker = "***" if improved else "   "
        print(f"  {stage_idx:>5}  {best_stats.mile:>7,}  {m:>6,}  {M_T:>6,}  "
              f"{a:>6}  {b:>6}  {k:>4}  {stage_bits:>5}  {bpm:>6.2f}  {stage_time:>4.1f}s  {marker}")
        sys.stdout.flush()

        stage_results.append({
            "stage": stage_idx,
            "improved": improved,
            "mile": best_stats.mile,
            "m_s": m,
            "m_t": M_T,
            "a": a, "b": b, "k": k,
            "recipe_bits": stage_bits,
            "bits_per_mile": round(bpm, 3),
        })

        if not improved:
            print(f"\n  No improvement at stage {stage_idx}.")
            break

    final_stats = residual_stats(current, target_digits)
    file_bits = len(raw) * 8
    overhead_bits = 193
    total_bits = overhead_bits + total_recipe_bits
    ratio = file_bits / total_bits if total_bits > 0 else 0
    total_mile_drop = init_stats.mile - final_stats.mile
    avg_bpm = total_recipe_bits / total_mile_drop if total_mile_drop > 0 else float('inf')

    print(f"\n  {'='*60}")
    print(f"  SUMMARY")
    print(f"  Stages:         {len(stage_results)}")
    print(f"  Mile:           {init_stats.mile:,} → {final_stats.mile:,}  (drop={total_mile_drop:,})")
    print(f"  Mismatch:       {init_stats.mismatch:,} → {final_stats.mismatch:,}")
    print(f"  Avg bits/mile:  {avg_bpm:.3f}")
    print(f"  Recipe bits:    {total_recipe_bits} = {total_recipe_bits//8} bytes")
    print(f"  Total w/ K:     {total_bits} bits = {total_bits//8} bytes")
    print(f"  File:           {len(raw):,} bytes")
    print(f"  Ratio:          {ratio:.1f}:1")
    if final_stats.mile > 0 and avg_bpm < float('inf'):
        proj_bits = overhead_bits + int(final_stats.mile * avg_bpm)
        proj_total = total_bits + proj_bits
        print(f"  Projected to 0: +{proj_bits} bits → total {proj_total} bits = {proj_total//8} bytes")
        print(f"  Projected ratio: {file_bits/proj_total:.1f}:1")

    return {
        "file_bytes": len(raw),
        "n_digits": n,
        "init_mile": init_stats.mile,
        "final_mile": final_stats.mile,
        "total_recipe_bits": total_recipe_bits,
        "avg_bits_per_mile": round(avg_bpm, 3),
        "ratio": round(ratio, 2),
        "stages": stage_results,
    }


def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument("files", nargs="+")
    p.add_argument("--stages", type=int, default=50)
    p.add_argument("--n-affine", type=int, default=200)
    p.add_argument("--top-ks", type=int, default=16)
    p.add_argument("--json-out")
    return p.parse_args()


def main():
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V36 — RESIDUAL-RESTRICTED AFFINE                     ║")
    print("║  Sigma acts only on source-displaced positions each stage   ║")
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
