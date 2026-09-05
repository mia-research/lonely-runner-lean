#!/usr/bin/env python3
"""
RIDE V14 - Scalar-address whole-file probe.

Purpose:
  Replace the explicit whole-file permutation map with a true scalar-address
  experiment:

    packet = { K params, delta, address, hash }

  where `address` selects one permutation from a deterministic whole-file family.

Current family:
  PCG32 + Fisher-Yates on the whole patched source stream.

Encoder:
  - actual K constant from thermodynamic manifold
  - deterministic frequency patch to exact target multiset
  - exact mile from cycle decomposition (used as search centre)
  - TSP-style constraint filter from high-index mismatches
  - scalar address search in the deterministic family

Decoder:
  - rebuild actual K
  - apply delta
  - materialise permutation at scalar address
  - verify raw hash

This is the clean bug-fix experiment for the user's objection:
  no full permutation map in the packet.
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
    deterministic_frequency_patch,
    build_perm_target_to_source,
    permutation_cycle_mile,
    encode_uvarint,
    encode_svarint,
    leading_zero_bytes,
    materialize_bytes_from_decimal,
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


def digit_hash(digits: bytearray) -> str:
    return hashlib.sha256(bytes(digits)).hexdigest()


def fisher_yates_bytearray(base: bytearray, seed: int) -> bytearray:
    rng = PCG32(seed)
    result = bytearray(base)
    for index in range(len(result) - 1, 0, -1):
        swap_index = rng.next_uniform(index + 1)
        result[index], result[swap_index] = result[swap_index], result[index]
    return result


def fisher_yates_with_constraints(base: bytearray, seed: int, constraints: list[tuple[int, int]]) -> bytearray | None:
    """
    Whole-file deterministic permutation with early bail.

    High positions are checked first because Fisher-Yates finalises from the end.
    """
    rng = PCG32(seed)
    result = bytearray(base)

    constraint_map = {position: value for position, value in constraints}
    positions = sorted(constraint_map.keys(), reverse=True)
    pos_index = 0
    next_check = positions[pos_index] if positions else -1

    for index in range(len(result) - 1, 0, -1):
        swap_index = rng.next_uniform(index + 1)
        result[index], result[swap_index] = result[swap_index], result[index]

        if index == next_check:
            if result[index] != constraint_map[index]:
                return None
            pos_index += 1
            next_check = positions[pos_index] if pos_index < len(positions) else -1

    if 0 in constraint_map and result[0] != constraint_map[0]:
        return None
    return result


def build_constraints(target_digits: bytearray, source_digits: bytearray, perm, max_constraints: int = 24) -> list[tuple[int, int]]:
    """
    TSP-style fingerprint:
      prefer mismatches near the end of the sequence so false seeds bail early,
      with displacement as a tie-breaker.
    """
    scored: list[tuple[tuple[int, int], tuple[int, int]]] = []
    for index in range(len(target_digits)):
        if target_digits[index] == source_digits[index]:
            continue
        displacement = abs(index - perm[index])
        scored.append(((index, displacement), (index, int(target_digits[index]))))

    scored.sort(reverse=True)
    constraints = [item for _score, item in scored[:max_constraints]]
    return constraints


def search_addresses(base_digits: bytearray, target_digits: bytearray, center: int, radius: int, constraints: list[tuple[int, int]]) -> dict:
    expected_hash = digit_hash(target_digits)
    start = time.perf_counter()
    scanned = 0
    constraint_passes = 0

    def candidate_order():
        yield center
        for offset in range(1, radius + 1):
            if center >= offset:
                yield center - offset
            yield center + offset

    seen = set()
    for address in candidate_order():
        if address < 0 or address in seen:
            continue
        seen.add(address)
        scanned += 1
        candidate = fisher_yates_with_constraints(base_digits, address, constraints)
        if candidate is None:
            continue
        constraint_passes += 1
        if digit_hash(candidate) == expected_hash:
            return {
                "hit": True,
                "address": address,
                "scanned": scanned,
                "constraint_passes": constraint_passes,
                "search_time_s": time.perf_counter() - start,
                "digits": candidate,
            }

    return {
        "hit": False,
        "address": None,
        "scanned": scanned,
        "constraint_passes": constraint_passes,
        "search_time_s": time.perf_counter() - start,
        "digits": None,
    }


def packet_size_bytes(params: tuple[int, int, int, int], delta: list[int], raw_length: int, leading_zeros: int, address: int) -> int:
    k_bytes = sum(len(encode_uvarint(value)) for value in params)
    delta_bytes = sum(len(encode_svarint(value)) for value in delta)
    meta_bytes = len(encode_uvarint(raw_length)) + len(encode_uvarint(leading_zeros))
    addr_bytes = max(1, (int(address).bit_length() + 7) // 8)
    hash_bytes = 32
    return k_bytes + delta_bytes + meta_bytes + addr_bytes + hash_bytes


def run_sanity_case() -> bool:
    print(f"\n{'=' * 72}")
    print("  Sanity case: scalar family exact hit")
    print(f"{'=' * 72}")

    base_counts = [4, 3, 3, 2, 3, 3, 2, 3, 3, 4]
    seed = construct_pivot_seed(base_counts)
    fixed, _steps, status = iterate_to_fixed(seed, max_iter=30)
    if fixed is None:
        print(f"  Failed to materialise sanity K source: {status}")
        return False

    base_digits = str_to_digits(fixed)
    known_address = 12345
    target_digits = fisher_yates_bytearray(base_digits, known_address)
    perm = build_perm_target_to_source(target_digits, base_digits)
    mile, _cycles = permutation_cycle_mile(perm)
    constraints = build_constraints(target_digits, base_digits, perm, max_constraints=16)
    result = search_addresses(base_digits, target_digits, center=known_address, radius=32, constraints=constraints)
    ok = bool(result["hit"] and result["address"] == known_address)
    print(
        f"  Known address={known_address} mile={mile:,} "
        f"scanned={result['scanned']:,} "
        f"constraint_passes={result['constraint_passes']:,} "
        f"verify={'OK' if ok else 'FAIL'}"
    )
    return ok


def run_whole_file(path: Path, radius: int) -> bool:
    raw = path.read_bytes()
    raw_hash = hashlib.sha256(raw).hexdigest()
    zero_prefix = leading_zero_bytes(raw)

    print(f"\n{'=' * 72}")
    print(f"  Whole-file scalar-address probe: {path.name}")
    print(f"{'=' * 72}")
    print(f"  Raw bytes: {len(raw):,}")

    t0 = time.perf_counter()
    decimal = binary_to_decimal_lossless(raw)
    target_counts = digit_counts(decimal)
    target_digits = str_to_digits(decimal)
    decimal_time = time.perf_counter() - t0
    print(f"  Decimal digits: {len(decimal):,}")
    print(f"  Decimal conversion: {decimal_time:.2f}s")

    t1 = time.perf_counter()
    v0, a, b, v9, l1 = nearest_thermo_params(target_counts)
    thermo_counts = thermo_counts_from_params(v0, a, b, v9)
    seed = construct_pivot_seed(thermo_counts)
    k_constant, steps, status = iterate_to_fixed(seed, max_iter=30)
    if k_constant is None:
        raise ValueError(f"K materialisation failed with status={status}")
    k_digits = str_to_digits(k_constant)
    patched_source, delta, edits = deterministic_frequency_patch(k_digits, target_counts)
    source_time = time.perf_counter() - t1

    t2 = time.perf_counter()
    perm = build_perm_target_to_source(target_digits, patched_source)
    mile, cycles = permutation_cycle_mile(perm)
    constraints = build_constraints(target_digits, patched_source, perm, max_constraints=24)
    analysis_time = time.perf_counter() - t2

    print(f"  Actual K params: v0={v0:,} a={a:,} b={b:,} v9={v9:,}")
    print(f"  K source + delta time: {source_time:.2f}s")
    print(f"  Frequency delta L1: {l1:,}")
    print(f"  Deterministic patch edits: {edits:,}")
    print(f"  Mile: {mile:,}  cycles: {cycles:,}")
    print(f"  Constraint count: {len(constraints)}")
    print(f"  Mile analysis: {analysis_time:.2f}s")

    search = search_addresses(patched_source, target_digits, center=mile, radius=radius, constraints=constraints)
    total_encode = decimal_time + source_time + analysis_time + search["search_time_s"]

    print("\nSearch")
    print(f"  Address centre: {mile:,}")
    print(f"  Radius: +/-{radius:,}")
    print(f"  Scanned: {search['scanned']:,}")
    print(f"  Constraint passes: {search['constraint_passes']:,}")
    print(f"  Search time: {search['search_time_s']:.2f}s")
    print(f"  Total encode time: {total_encode:.2f}s")

    if not search["hit"]:
        print("  Result: no exact scalar address found in the searched window")
        return False

    address = int(search["address"])
    packet_bytes = packet_size_bytes((v0, a, b, v9), delta, len(raw), zero_prefix, address)

    print("\nPacket")
    print(f"  Address: {address:,}")
    print(f"  Total recipe: {packet_bytes:,}B")
    print(f"  Raw/recipe ratio: {len(raw) / packet_bytes:.3f}x")

    t3 = time.perf_counter()
    reconstructed_digits = fisher_yates_bytearray(patched_source, address)
    reconstructed_bytes = materialize_bytes_from_decimal(reconstructed_digits, len(raw), zero_prefix)
    decode_time = time.perf_counter() - t3

    ok = reconstructed_bytes == raw and hashlib.sha256(reconstructed_bytes).hexdigest() == raw_hash
    print("\nDecode")
    print(f"  Decode time: {decode_time:.2f}s")
    print(f"  Verify: {'BIT-PERFECT' if ok else 'FAILED'}")
    return ok


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Scalar-address whole-file probe")
    parser.add_argument("file", help="Whole file to test")
    parser.add_argument("--radius", type=int, default=50000, help="Search radius around the mile/address centre")
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V14 - SCALAR ADDRESS PROBE                            ║")
    print("║  actual K + delta + single whole-file address family        ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    sanity_ok = run_sanity_case()
    file_ok = run_whole_file(Path(args.file).expanduser(), args.radius)
    return 0 if sanity_ok and file_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
