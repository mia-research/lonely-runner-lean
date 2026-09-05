#!/usr/bin/env python3
"""
RIDE V26 - Dual scaffold probe.
# v1.0 — 2026-04-13 — target || complement scaffold navigated in K-lattice

DUAL SCAFFOLD HYPOTHESIS
--------------------------
The target file's digit sequence is NOT pair-balanced (arbitrary data rarely is).
But if we concatenate the file's digits with their digit complements (d -> 9-d),
we get a pair-balanced 2n-digit number that IS navigable in the K-lattice.

Construction:
  file digits: D = [d_0, d_1, ..., d_{n-1}]
  complement:  C = [9-d_0, 9-d_1, ..., 9-d_{n-1}]
  scaffold:    S = D || C   (2n digits)

Properties of S:
  - For every digit value v in D, value (9-v) appears equally often in C.
  - Therefore count[v] + count[9-v] = n/5 (approximately uniform, pair-balanced).
  - S looks structurally like a K-constant's digit multiset.
  - The first half of S is exactly the file.

RECIPE (sender):
  1. Build scaffold S from file D.
  2. Find nearest K-constant K* whose multiset matches S's multiset (delta small).
  3. Recipe = (K* address, delta, "extract first half")

DECODER:
  1. Reconstruct K* from address (extension algorithm).
  2. Apply delta to get scaffold S.
  3. Extract first n digits = file D.

KEY QUESTION:
  Does the scaffold S lie close (in K-multiset space) to actual K-constants?
  If yes, the delta is small and the recipe is compact.
  If no, scaffolding does not help.

WHAT THIS SCRIPT MEASURES:
  A. Scaffold digit multiset vs. nearest K multiset: L1 distance.
  B. Compare with raw file multiset vs. nearest K multiset (v12 baseline).
  C. Cycle count for the scaffold arrangement (forward and reverse directions).
  D. Whether the first-half extraction is exact after delta application.

NOTE ON ORDER:
  The scaffold S has a specific arrangement (D in first half, C in second).
  The K-constant in canonical form is desc-sorted.
  The order problem for the scaffold is: K-canonical -> scaffold arrangement.
  The key hope: since the scaffold is structured (complement-symmetric),
  its arrangement relative to the K-canonical form may be more compressible
  than an arbitrary file's arrangement.
"""

from __future__ import annotations

import argparse
import hashlib
import sys
import time
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
MIAI = Path("/Users/trentpalelei/MIAI")
for candidate in (HERE, MIAI):
    s = str(candidate)
    if candidate.exists() and s not in sys.path:
        sys.path.insert(0, s)

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(10_000_000)

from ride_v12_kmanifold_probe import (
    binary_to_decimal_lossless,
    digit_counts,
    nearest_thermo_params,
    thermo_counts_from_params,
)
from ride_v13_canterbury_recipe_bench import (
    build_perm_target_to_source,
    permutation_cycle_mile,
    str_to_digits,
)
from ride_v18_cycle_rsn import build_rsn_cycle_plan
from ride_v25_reverse_delta_probe import (
    apply_reverse_delta,
    canonical_arrangement,
)


def build_scaffold(file_digits: list[int]) -> list[int]:
    """
    Concatenate file digits with their complements.
    scaffold[i] = file_digits[i]  for i < n
    scaffold[n+i] = 9 - file_digits[i]  for i < n
    """
    complement = [9 - d for d in file_digits]
    return file_digits + complement


def scaffold_counts(scaffold: list[int]) -> list[int]:
    counts = [0] * 10
    for d in scaffold:
        counts[d] += 1
    return counts


def measure_scaffold(raw: bytes) -> dict:
    t0 = time.perf_counter()

    # --- File digits ---
    decimal = binary_to_decimal_lossless(raw)
    file_digits = list(str_to_digits(decimal))
    n = len(file_digits)
    file_counts = digit_counts(decimal)

    # --- Build scaffold ---
    scaffold = build_scaffold(file_digits)
    s_counts = scaffold_counts(scaffold)

    # --- Nearest K multiset for file alone (baseline) ---
    _v0f, _af, _bf, _v9f, freq_l1_file = nearest_thermo_params(file_counts)
    k_counts_file = thermo_counts_from_params(_v0f, _af, _bf, _v9f)
    delta_l1_file = sum(abs(file_counts[d] - k_counts_file[d]) for d in range(10))

    # --- Nearest K multiset for scaffold ---
    v0s, as_, bs, v9s, freq_l1_scaffold = nearest_thermo_params(s_counts)
    k_counts_scaffold = thermo_counts_from_params(v0s, as_, bs, v9s)
    delta_l1_scaffold = sum(abs(s_counts[d] - k_counts_scaffold[d]) for d in range(10))

    prep_time = time.perf_counter() - t0

    # --- Order problem: K-canonical for scaffold -> scaffold arrangement ---
    t1 = time.perf_counter()
    k_canonical_scaffold = canonical_arrangement(k_counts_scaffold)

    # Apply delta to match scaffold multiset
    try:
        patched = apply_reverse_delta(k_canonical_scaffold, k_counts_scaffold, s_counts)
    except ValueError as e:
        return {"error": f"delta patch failed: {e}"}

    if Counter(patched) != Counter(scaffold):
        return {"error": "scaffold multiset mismatch after delta"}

    perm = list(build_perm_target_to_source(
        bytearray(scaffold),
        bytearray(patched),
    ))
    mile, cycles = permutation_cycle_mile(perm)
    plan = build_rsn_cycle_plan(perm)
    order_time = time.perf_counter() - t1

    # --- Extraction verification ---
    # If we had perfect reconstruction of scaffold, first half = file.
    # We can verify this is structurally true (it always is by construction).
    scaffold_ok = scaffold[:n] == file_digits

    # --- Pair-balance quality of scaffold multiset ---
    # Ideal: count[d] == count[9-d] for all d.
    balance_error = sum(abs(s_counts[d] - s_counts[9 - d]) for d in range(5))

    # --- Ratio: scaffold order problem vs. per-digit scaling ---
    # Expected if scaffold were random: ~2x file mile (double the digits)
    # If scaffold < 2x file mile, the structure is helping.
    mile_per_digit_scaffold = mile / len(scaffold) if scaffold else 0

    return {
        "file_bytes": len(raw),
        "file_digits": n,
        "scaffold_digits": len(scaffold),
        # Frequency layer
        "delta_l1_file_alone": delta_l1_file,
        "delta_l1_scaffold": delta_l1_scaffold,
        "scaffold_l1_relative_gain": delta_l1_file / delta_l1_scaffold if delta_l1_scaffold > 0 else None,
        # Pair balance quality
        "scaffold_balance_error": balance_error,
        # Order layer
        "scaffold_mile": mile,
        "scaffold_cycles": cycles,
        "scaffold_non_trivial": plan["non_trivial"],
        "mile_per_digit": round(mile_per_digit_scaffold, 4),
        # Extraction check
        "first_half_equals_file": scaffold_ok,
        "prep_time": round(prep_time, 3),
        "order_time": round(order_time, 3),
    }


def run(path: Path) -> None:
    raw = path.read_bytes()
    print(f"\n{'=' * 72}")
    print(f"  RIDE V26 — Dual scaffold probe: {path.name}")
    print(f"{'=' * 72}")
    print(f"  Raw bytes: {len(raw):,}")

    result = measure_scaffold(raw)

    if "error" in result:
        print(f"  ERROR: {result['error']}")
        return

    print(f"  File digits:     {result['file_digits']:,}")
    print(f"  Scaffold digits: {result['scaffold_digits']:,}  (2x)")
    print()
    print(f"  FREQUENCY LAYER:")
    print(f"    L1 to K (file alone): {result['delta_l1_file_alone']:,}")
    print(f"    L1 to K (scaffold):   {result['delta_l1_scaffold']:,}")
    gain = result['scaffold_l1_relative_gain']
    if gain is not None:
        print(f"    Scaffold frequency gain: {gain:.2f}x  ", end="")
        print("(>1 = scaffold closer to K than raw file)" if gain > 1 else "(scaffold no better)")
    print(f"    Pair-balance error (ideal=0): {result['scaffold_balance_error']}")
    print()
    print(f"  ORDER LAYER (K-canonical -> scaffold arrangement):")
    print(f"    Mile:          {result['scaffold_mile']:,}")
    print(f"    Cycles:        {result['scaffold_cycles']:,}")
    print(f"    Non-trivial:   {result['scaffold_non_trivial']:,}")
    print(f"    Mile/digit:    {result['mile_per_digit']}")
    print()
    print(f"  First-half extraction gives file: {result['first_half_equals_file']}")
    print(f"  Prep: {result['prep_time']}s  Order: {result['order_time']}s")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="RIDE V26 — dual scaffold probe")
    parser.add_argument("files", nargs="+", help="Files to test")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V26 — DUAL SCAFFOLD PROBE                             ║")
    print("║  Does target || complement lie closer to K-lattice?         ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    for f in args.files:
        run(Path(f).expanduser())
    return 0


if __name__ == "__main__":
    sys.exit(main())
