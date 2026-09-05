#!/usr/bin/env python3
"""
RIDE V16 - Whole-file perturbation-step probe.

This matches the user's intended model more closely than V14/V15:
  - whole file is treated as one number
  - actual thermodynamic K constant is materialised
  - deterministic frequency delta restores the exact multiset
  - a single whole-file perturbation orbit is shared by encoder/decoder
  - `steps` means how many perturbations along that orbit were applied

Packet if a hit exists:
  { K params, delta, steps, hash }

Current orbit family:
  - hash-seeded stream of whole-file transpositions
  - one swap == one perturbation step

This makes the "mile" and the "address" live in the same unit:
  both are transposition counts.
"""

from __future__ import annotations

import argparse
import hashlib
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


def pick_constraints(target_digits: bytearray, source_digits: bytearray, perm, max_constraints: int = 32) -> list[tuple[int, int]]:
    scored: list[tuple[tuple[int, int], tuple[int, int]]] = []
    for index in range(len(target_digits)):
        if target_digits[index] == source_digits[index]:
            continue
        displacement = abs(index - perm[index])
        scored.append(((displacement, index), (index, int(target_digits[index]))))
    scored.sort(reverse=True)
    return [item for _score, item in scored[:max_constraints]]


def apply_steps(base: bytearray, seed: int, steps: int) -> bytearray:
    rng = PCG32(seed)
    state = bytearray(base)
    n = len(state)
    for _ in range(steps):
        i = rng.next_uniform(n)
        j = rng.next_uniform(n - 1)
        if j >= i:
            j += 1
        state[i], state[j] = state[j], state[i]
    return state


def search_orbit_window(
    base: bytearray,
    target_digits: bytearray,
    seed: int,
    center: int,
    radius: int,
    constraints: list[tuple[int, int]],
) -> dict:
    expected_hash = hashlib.sha256(bytes(target_digits)).hexdigest()
    lower = max(0, center - radius)
    upper = center + radius

    rng = PCG32(seed)
    state = bytearray(base)
    n = len(state)

    start = time.perf_counter()
    constraint_passes = 0
    hash_checks = 0

    def constraints_match() -> bool:
        for index, value in constraints:
            if state[index] != value:
                return False
        return True

    if lower == 0 and constraints_match():
        constraint_passes += 1
        hash_checks += 1
        if hashlib.sha256(bytes(state)).hexdigest() == expected_hash:
            return {
                "hit": True,
                "steps": 0,
                "scanned": 1,
                "constraint_passes": constraint_passes,
                "hash_checks": hash_checks,
                "search_time_s": time.perf_counter() - start,
            }

    scanned = 1 if lower == 0 else 0

    for step in range(1, upper + 1):
        i = rng.next_uniform(n)
        j = rng.next_uniform(n - 1)
        if j >= i:
            j += 1
        state[i], state[j] = state[j], state[i]

        if step < lower:
            continue

        scanned += 1
        if not constraints_match():
            continue
        constraint_passes += 1
        hash_checks += 1
        if hashlib.sha256(bytes(state)).hexdigest() == expected_hash:
            return {
                "hit": True,
                "steps": step,
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
    steps_bytes = len(encode_uvarint(steps))
    hash_bytes = 32
    return k_bytes + delta_bytes + meta_bytes + steps_bytes + hash_bytes


def run_sanity(known_steps: int = 12345, radius: int = 256) -> bool:
    print(f"\n{'=' * 72}")
    print("  Sanity case: whole-file perturbation orbit")
    print(f"{'=' * 72}")

    counts = [4, 3, 3, 2, 3, 3, 2, 3, 3, 4]
    seed_str = construct_pivot_seed(counts)
    k_constant, _steps, status = iterate_to_fixed(seed_str, max_iter=30)
    if k_constant is None:
        print(f"  Failed to materialise sanity K constant: {status}")
        return False

    base = bytearray(str_to_digits(k_constant))
    target = apply_steps(base, seed=0xC0FFEE1234, steps=known_steps)
    perm = build_perm_target_to_source(target, base)
    mile, cycles = permutation_cycle_mile(perm)
    constraints = pick_constraints(target, base, perm, max_constraints=12)
    search = search_orbit_window(base, target, seed=0xC0FFEE1234, center=known_steps, radius=radius, constraints=constraints)

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
    orbit_seed = orbit_seed_from_hash(raw_hash)

    print(f"\n{'=' * 72}")
    print(f"  Whole-file perturbation-step probe: {path.name}")
    print(f"{'=' * 72}")
    print(f"  Raw bytes: {len(raw):,}")

    t0 = time.perf_counter()
    decimal = binary_to_decimal_lossless(raw)
    target_counts = digit_counts(decimal)
    target_digits = bytearray(str_to_digits(decimal))
    decimal_time = time.perf_counter() - t0
    print(f"  Decimal digits: {len(decimal):,}")
    print(f"  Decimal conversion: {decimal_time:.2f}s")

    t1 = time.perf_counter()
    v0, a, b, v9, l1 = nearest_thermo_params(target_counts)
    thermo_counts = thermo_counts_from_params(v0, a, b, v9)
    seed = construct_pivot_seed(thermo_counts)
    k_constant, k_steps, status = iterate_to_fixed(seed, max_iter=30)
    if k_constant is None:
        raise ValueError(f"K materialisation failed with status={status}")
    k_digits = bytearray(str_to_digits(k_constant))
    patched_source, delta, edits = deterministic_frequency_patch(k_digits, target_counts)
    source_time = time.perf_counter() - t1

    t2 = time.perf_counter()
    perm = build_perm_target_to_source(target_digits, patched_source)
    mile, cycles = permutation_cycle_mile(perm)
    constraints = pick_constraints(target_digits, patched_source, perm, max_constraints=32)
    analysis_time = time.perf_counter() - t2

    print(f"  Actual K params: v0={v0:,} a={a:,} b={b:,} v9={v9:,}")
    print(f"  K source + delta time: {source_time:.2f}s  ({k_steps} Kaprekar steps)")
    print(f"  Frequency delta L1: {l1:,}")
    print(f"  Deterministic patch edits: {edits:,}")
    print(f"  Orbit seed: 0x{orbit_seed:016x}")
    print(f"  Mile: {mile:,}  cycles: {cycles:,}")
    print(f"  Constraint count: {len(constraints)}")
    print(f"  Mile analysis: {analysis_time:.2f}s")

    search = search_orbit_window(
        patched_source,
        target_digits,
        orbit_seed,
        center=mile,
        radius=radius,
        constraints=constraints,
    )
    total_encode = decimal_time + source_time + analysis_time + search["search_time_s"]

    print("\nSearch")
    print(f"  Address centre (mile): {mile:,}")
    print(f"  Radius: +/-{radius:,}")
    print(f"  Scanned: {search['scanned']:,}")
    print(f"  Constraint passes: {search['constraint_passes']:,}")
    print(f"  Hash checks: {search['hash_checks']:,}")
    print(f"  Search time: {search['search_time_s']:.2f}s")
    print(f"  Total encode time: {total_encode:.2f}s")

    if not search["hit"]:
        print("  Result: no exact whole-file step-count hit in the searched window")
        return False

    steps_needed = int(search["steps"])
    packet_bytes = packet_size_bytes((v0, a, b, v9), delta, len(raw), zero_prefix, steps_needed)

    print("\nPacket")
    print(f"  Steps needed: {steps_needed:,}")
    print(f"  Total recipe: {packet_bytes:,}B")
    print(f"  Raw/recipe ratio: {len(raw) / packet_bytes:.3f}x")

    t3 = time.perf_counter()
    reconstructed_digits = apply_steps(patched_source, orbit_seed, steps_needed)
    reconstructed_bytes = materialize_bytes_from_decimal(reconstructed_digits, len(raw), zero_prefix)
    decode_time = time.perf_counter() - t3

    ok = reconstructed_bytes == raw and hashlib.sha256(reconstructed_bytes).hexdigest() == raw_hash
    print("\nDecode")
    print(f"  Decode time: {decode_time:.2f}s")
    print(f"  Verify: {'BIT-PERFECT' if ok else 'FAILED'}")
    return ok


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Whole-file perturbation-step probe")
    parser.add_argument("file", help="Whole file to test")
    parser.add_argument("--radius", type=int, default=100000, help="Search radius around the exact mile")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V16 - WHOLE-FILE PERTURBATION STEPS                   ║")
    print("║  actual K + delta + whole-file step count                   ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    sanity_ok = run_sanity()
    file_ok = run_whole_file(Path(args.file).expanduser(), args.radius)
    return 0 if sanity_ok and file_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
