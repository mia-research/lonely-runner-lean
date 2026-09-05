#!/usr/bin/env python3
"""
RIDE V19 - Decoder-known pivot-cycle orbit family.

This is the first attempt to turn the V18 cycle insight into a shared family:

  - V18 showed that real whole-file permutations collapse into a tiny number of
    enormous stressed cycles with stable pivots.
  - So instead of random pair-swaps, the decoder-known orbit uses a small set of
    persistent pivots.
  - Each pivot walks a deterministic partner orbit across the whole file.
  - One step == one pivot-star transposition.

Packet if a hit exists:
  { K params, delta, family_id, steps, hash }

This still may not be the final family, but it is cycle-shaped rather than
generic-random, and both sides can reproduce it from K + hash.
"""

from __future__ import annotations

import argparse
import hashlib
import math
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
MIAI = Path("/Users/trentpalelei/MIAI")
for candidate in (HERE, MIAI):
    candidate_str = str(candidate)
    if candidate.exists() and candidate_str not in sys.path:
        sys.path.insert(0, candidate_str)

from ride_v12_kmanifold_probe import (
    binary_to_decimal_lossless,
    construct_pivot_seed,
    digit_counts,
    iterate_to_fixed,
    nearest_thermo_params,
    thermo_counts_from_params,
)
from ride_v13_canterbury_recipe_bench import (
    build_perm_target_to_source,
    deterministic_frequency_patch,
    encode_svarint,
    encode_uvarint,
    leading_zero_bytes,
    materialize_bytes_from_decimal,
    permutation_cycle_mile,
    str_to_digits,
)


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(10_000_000)


class PCG32:
    __slots__ = ("state", "inc")

    def __init__(self, seed: int):
        self.state = (int(seed) | 1) & 0xFFFFFFFFFFFFFFFF
        self.inc = 1
        for _ in range(10):
            self.next()

    def next(self) -> int:
        old = self.state
        self.state = (old * 6364136223846793005 + self.inc) & 0xFFFFFFFFFFFFFFFF
        xorshifted = int(((old >> 18) ^ old) >> 27) & 0xFFFFFFFF
        rot = int(old >> 59) & 0x1F
        return ((xorshifted >> rot) | (xorshifted << ((-rot) & 31))) & 0xFFFFFFFF

    def next_uniform(self, bound: int) -> int:
        threshold = (-bound % bound) & 0xFFFFFFFF
        while True:
            value = self.next()
            if value >= threshold:
                return value % bound


def orbit_seed_from_hash(raw_hash_hex: str) -> int:
    return int(raw_hash_hex[:16], 16)


def materialise_source(raw: bytes) -> tuple[bytearray, bytearray, tuple[int, int, int, int], list[int], int]:
    decimal = binary_to_decimal_lossless(raw)
    target_counts = digit_counts(decimal)
    target_digits = bytearray(str_to_digits(decimal))
    v0, a, b, v9, l1 = nearest_thermo_params(target_counts)
    thermo_counts = thermo_counts_from_params(v0, a, b, v9)
    seed = construct_pivot_seed(thermo_counts)
    k_constant, _steps, status = iterate_to_fixed(seed, max_iter=30)
    if k_constant is None:
        raise ValueError(f"K materialisation failed with status={status}")
    k_digits = bytearray(str_to_digits(k_constant))
    patched_source, delta, _edits = deterministic_frequency_patch(k_digits, target_counts)
    return patched_source, target_digits, (v0, a, b, v9), delta, l1


def pick_constraints(target_digits: bytearray, source_digits: bytearray, perm, max_constraints: int = 32) -> list[tuple[int, int]]:
    scored: list[tuple[tuple[int, int], tuple[int, int]]] = []
    for index in range(len(target_digits)):
        if target_digits[index] == source_digits[index]:
            continue
        displacement = abs(index - perm[index])
        scored.append(((displacement, index), (index, int(target_digits[index]))))
    scored.sort(reverse=True)
    return [item for _score, item in scored[:max_constraints]]


def choose_coprime_stride(rng: PCG32, n: int) -> int:
    stride = rng.next_uniform(max(2, n - 1)) + 1
    while math.gcd(stride, n) != 1:
        stride += 1
        if stride >= n:
            stride = 1
    return stride


def derive_pivot_family(seed: int, n: int, pivot_count: int = 16) -> dict:
    rng = PCG32(seed)
    pivots: list[int] = []
    used = set()

    scaffold = [
        0,
        n // 2,
        n // 4,
        (3 * n) // 4,
        n // 8,
        (3 * n) // 8,
        (5 * n) // 8,
        (7 * n) // 8,
        n - 1,
    ]
    for pivot in scaffold:
        if 0 <= pivot < n and pivot not in used:
            pivots.append(pivot)
            used.add(pivot)
        if len(pivots) >= min(pivot_count, n):
            break

    while len(pivots) < min(pivot_count, n):
        pivot = rng.next_uniform(n)
        if pivot in used:
            continue
        pivots.append(pivot)
        used.add(pivot)

    offsets: list[int] = []
    strides: list[int] = []
    for _pivot in pivots:
        offsets.append(rng.next_uniform(n))
        strides.append(choose_coprime_stride(rng, n))

    return {
        "pivots": pivots,
        "offsets": offsets,
        "strides": strides,
    }


def orbit_swap_for_step(family: dict, n: int, step: int) -> tuple[int, int]:
    pivots = family["pivots"]
    offsets = family["offsets"]
    strides = family["strides"]
    pivot_slot = step % len(pivots)
    round_idx = step // len(pivots)
    pivot = pivots[pivot_slot]
    partner = (offsets[pivot_slot] + round_idx * strides[pivot_slot]) % n
    if partner == pivot:
        partner = (partner + strides[pivot_slot]) % n
    return pivot, partner


def apply_steps(base: bytearray, family: dict, steps: int) -> bytearray:
    state = bytearray(base)
    n = len(state)
    for step in range(steps):
        i, j = orbit_swap_for_step(family, n, step)
        state[i], state[j] = state[j], state[i]
    return state


def search_orbit_window(
    base: bytearray,
    target_digits: bytearray,
    family: dict,
    center: int,
    radius: int,
    constraints: list[tuple[int, int]],
) -> dict:
    expected_hash = hashlib.sha256(bytes(target_digits)).hexdigest()
    lower = max(0, center - radius)
    upper = center + radius
    state = bytearray(base)
    n = len(state)
    start = time.perf_counter()
    scanned = 0
    constraint_passes = 0
    hash_checks = 0

    def constraints_match() -> bool:
        for index, value in constraints:
            if state[index] != value:
                return False
        return True

    if lower == 0:
        scanned += 1
        if constraints_match():
            constraint_passes += 1
            hash_checks += 1
            if hashlib.sha256(bytes(state)).hexdigest() == expected_hash:
                return {
                    "hit": True,
                    "steps": 0,
                    "scanned": scanned,
                    "constraint_passes": constraint_passes,
                    "hash_checks": hash_checks,
                    "search_time_s": time.perf_counter() - start,
                }

    for step in range(upper):
        i, j = orbit_swap_for_step(family, n, step)
        state[i], state[j] = state[j], state[i]
        current_steps = step + 1
        if current_steps < lower:
            continue
        scanned += 1
        if not constraints_match():
            continue
        constraint_passes += 1
        hash_checks += 1
        if hashlib.sha256(bytes(state)).hexdigest() == expected_hash:
            return {
                "hit": True,
                "steps": current_steps,
                "scanned": scanned,
                "constraint_passes": constraint_passes,
                "hash_checks": hash_checks,
                "search_time_s": time.perf_counter() - start,
            }

    return {
        "hit": False,
        "steps": None,
        "scanned": scanned,
        "constraint_passes": constraint_passes,
        "hash_checks": hash_checks,
        "search_time_s": time.perf_counter() - start,
    }


def packet_size_bytes(params: tuple[int, int, int, int], delta: list[int], raw_length: int, leading_zeros: int, steps: int) -> int:
    k_bytes = sum(len(encode_uvarint(value)) for value in params)
    delta_bytes = sum(len(encode_svarint(value)) for value in delta)
    meta_bytes = len(encode_uvarint(raw_length)) + len(encode_uvarint(leading_zeros))
    family_bytes = 1
    steps_bytes = len(encode_uvarint(steps))
    hash_bytes = 32
    return k_bytes + delta_bytes + meta_bytes + family_bytes + steps_bytes + hash_bytes


def run_sanity(known_steps: int = 12345, radius: int = 256) -> bool:
    print(f"\n{'=' * 72}")
    print("  Sanity case: pivot-cycle orbit")
    print(f"{'=' * 72}")

    counts = [4, 3, 3, 2, 3, 3, 2, 3, 3, 4]
    seed_str = construct_pivot_seed(counts)
    k_constant, _steps, status = iterate_to_fixed(seed_str, max_iter=30)
    if k_constant is None:
        print(f"  Failed to materialise sanity K constant: {status}")
        return False

    base = bytearray(str_to_digits(k_constant))
    family = derive_pivot_family(0xBEEF1234, len(base), pivot_count=4)
    target = apply_steps(base, family, known_steps)
    perm = build_perm_target_to_source(target, base)
    mile, cycles = permutation_cycle_mile(perm)
    constraints = pick_constraints(target, base, perm, max_constraints=12)
    search = search_orbit_window(base, target, family, center=known_steps, radius=radius, constraints=constraints)
    ok = bool(search["hit"] and search["steps"] == known_steps)
    print(
        f"  Known steps={known_steps:,}  mile={mile:,}  cycles={cycles:,}  "
        f"scanned={search['scanned']:,}  hash_checks={search['hash_checks']:,}  "
        f"verify={'OK' if ok else 'FAIL'}"
    )
    return ok


def run_whole_file(path: Path, radius: int) -> bool:
    raw = path.read_bytes()
    raw_hash = hashlib.sha256(raw).hexdigest()
    zero_prefix = leading_zero_bytes(raw)
    seed = orbit_seed_from_hash(raw_hash)

    print(f"\n{'=' * 72}")
    print(f"  Whole-file pivot-cycle orbit: {path.name}")
    print(f"{'=' * 72}")
    print(f"  Raw bytes: {len(raw):,}")

    t0 = time.perf_counter()
    source_digits, target_digits, params, delta, l1 = materialise_source(raw)
    prep_time = time.perf_counter() - t0

    t1 = time.perf_counter()
    perm = build_perm_target_to_source(target_digits, source_digits)
    mile, cycles = permutation_cycle_mile(perm)
    constraints = pick_constraints(target_digits, source_digits, perm, max_constraints=32)
    family = derive_pivot_family(seed, len(source_digits), pivot_count=16)
    analysis_time = time.perf_counter() - t1

    print(f"  K params: v0={params[0]:,} a={params[1]:,} b={params[2]:,} v9={params[3]:,}")
    print(f"  Frequency delta L1: {l1:,}")
    print(f"  Prep time: {prep_time:.2f}s")
    print(f"  Family seed: 0x{seed:016x}")
    print(f"  Family pivots: {len(family['pivots'])}")
    print(f"  Mile: {mile:,}  cycles: {cycles:,}")
    print(f"  Constraint count: {len(constraints)}")
    print(f"  Family analysis: {analysis_time:.2f}s")

    search = search_orbit_window(source_digits, target_digits, family, center=mile, radius=radius, constraints=constraints)
    total_encode = prep_time + analysis_time + search["search_time_s"]

    print("\nSearch")
    print(f"  Address centre (mile): {mile:,}")
    print(f"  Radius: +/-{radius:,}")
    print(f"  Scanned: {search['scanned']:,}")
    print(f"  Constraint passes: {search['constraint_passes']:,}")
    print(f"  Hash checks: {search['hash_checks']:,}")
    print(f"  Search time: {search['search_time_s']:.2f}s")
    print(f"  Total encode time: {total_encode:.2f}s")

    if not search["hit"]:
        print("  Result: no exact pivot-cycle hit in the searched window")
        return False

    steps_needed = int(search["steps"])
    packet_bytes = packet_size_bytes(params, delta, len(raw), zero_prefix, steps_needed)
    print("\nPacket")
    print(f"  Steps needed: {steps_needed:,}")
    print(f"  Total recipe: {packet_bytes:,}B")
    print(f"  Raw/recipe ratio: {len(raw) / packet_bytes:.3f}x")

    t2 = time.perf_counter()
    reconstructed_digits = apply_steps(source_digits, family, steps_needed)
    reconstructed_bytes = materialize_bytes_from_decimal(reconstructed_digits, len(raw), zero_prefix)
    decode_time = time.perf_counter() - t2

    ok = reconstructed_bytes == raw and hashlib.sha256(reconstructed_bytes).hexdigest() == raw_hash
    print("\nDecode")
    print(f"  Decode time: {decode_time:.2f}s")
    print(f"  Verify: {'BIT-PERFECT' if ok else 'FAILED'}")
    return ok


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Decoder-known pivot-cycle orbit probe")
    parser.add_argument("file", help="Whole file to test")
    parser.add_argument("--radius", type=int, default=100000)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V19 - PIVOT-CYCLE ORBIT FAMILY                        ║")
    print("║  decoder-known persistent pivots                            ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    sanity_ok = run_sanity()
    file_ok = run_whole_file(Path(args.file).expanduser(), args.radius)
    return 0 if sanity_ok and file_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
