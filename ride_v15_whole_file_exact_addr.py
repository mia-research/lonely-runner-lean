#!/usr/bin/env python3
"""
RIDE V15 - Whole-file exact scalar-address benchmark.

This fixes the concrete bug in V13:
  it no longer stores the explicit whole-file permutation map.

Exact packet shape:
  { K params, delta, raw_length, leading_zeros, address, hash }

Where:
  - K params materialise the nearest actual thermodynamic K constant
  - delta patches K to the exact file digit multiset
  - address is the exact scalar rank within that digit multiset
  - hash verifies the raw-byte reconstruction

This is the honest exact scalar-address baseline.
It is not yet the smaller TSP-guided address family the user wants, but it
eliminates the wrong O(N) source-index payload from the packet.
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
    encode_svarint,
    encode_uvarint,
    leading_zero_bytes,
    materialize_bytes_from_decimal,
    str_to_digits,
)
from ride_v6_kcoords_addr import count_digits, rank_permutation_fast, unrank_permutation_fast


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(10_000_000)


def packet_size_bytes(
    params: tuple[int, int, int, int],
    delta: list[int],
    raw_length: int,
    leading_zeros: int,
    address: int,
) -> dict[str, int]:
    k_bytes = sum(len(encode_uvarint(value)) for value in params)
    delta_bytes = sum(len(encode_svarint(value)) for value in delta)
    meta_bytes = len(encode_uvarint(raw_length)) + len(encode_uvarint(leading_zeros))
    addr_bits = max(1, int(address).bit_length())
    addr_bytes = (addr_bits + 7) // 8
    hash_bytes = 32
    total = k_bytes + delta_bytes + meta_bytes + addr_bytes + hash_bytes
    return {
        "k_bytes": k_bytes,
        "delta_bytes": delta_bytes,
        "meta_bytes": meta_bytes,
        "addr_bits": addr_bits,
        "addr_bytes": addr_bytes,
        "hash_bytes": hash_bytes,
        "total_bytes": total,
    }


def run_benchmark(path: Path) -> bool:
    raw = path.read_bytes()
    raw_hash = hashlib.sha256(raw).hexdigest()
    zero_prefix = leading_zero_bytes(raw)

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V15 - WHOLE-FILE EXACT SCALAR ADDRESS                 ║")
    print("║  actual K + delta + exact address (no permutation map)      ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print(f"\nFile: {path}")
    print(f"Raw bytes: {len(raw):,}")

    t0 = time.perf_counter()
    decimal = binary_to_decimal_lossless(raw)
    target_counts = digit_counts(decimal)
    target_digits = str_to_digits(decimal)
    decimal_time = time.perf_counter() - t0

    print(f"Decimal digits: {len(decimal):,}")
    print(f"Lossless decimal conversion: {decimal_time:.2f}s")

    t1 = time.perf_counter()
    v0, a, b, v9, l1 = nearest_thermo_params(target_counts)
    thermo_counts = thermo_counts_from_params(v0, a, b, v9)
    seed = construct_pivot_seed(thermo_counts)
    k_constant, steps, status = iterate_to_fixed(seed, max_iter=30)
    if k_constant is None:
        raise ValueError(f"Kaprekar iteration failed with status={status}")
    k_digits = str_to_digits(k_constant)
    patched_source, delta, edits = deterministic_frequency_patch(k_digits, target_counts)
    source_time = time.perf_counter() - t1

    if count_digits(target_digits) != count_digits(patched_source):
        raise ValueError("patched source multiset does not match target multiset")

    t2 = time.perf_counter()
    address = rank_permutation_fast(target_digits, target_counts)
    rank_time = time.perf_counter() - t2

    encode_time = decimal_time + source_time + rank_time
    size = packet_size_bytes((v0, a, b, v9), delta, len(raw), zero_prefix, address)

    print("\nEncode")
    print(f"  Actual K params: v0={v0:,} a={a:,} b={b:,} v9={v9:,}")
    print(f"  Actual K materialization + delta: {source_time:.2f}s  ({steps} Kaprekar steps)")
    print(f"  Frequency delta L1: {l1:,}")
    print(f"  Deterministic patch edits: {edits:,} digits")
    print(f"  Address rank time: {rank_time:.2f}s")
    print(f"  Total encode time: {encode_time:.2f}s")

    print("\nPacket")
    print(f"  K params: {size['k_bytes']:,}B")
    print(f"  Delta: {size['delta_bytes']:,}B")
    print(f"  Meta: {size['meta_bytes']:,}B")
    print(f"  Address: {size['addr_bits']:,} bits = {size['addr_bytes']:,}B")
    print(f"  SHA-256: {size['hash_bytes']:,}B")
    print(f"  Total recipe: {size['total_bytes']:,}B")
    print(f"  Raw/recipe ratio: {len(raw) / size['total_bytes']:.3f}x")

    t3 = time.perf_counter()
    reconstructed_digits = bytearray(unrank_permutation_fast(address, target_counts, len(target_digits)))
    unrank_time = time.perf_counter() - t3

    t4 = time.perf_counter()
    reconstructed_bytes = materialize_bytes_from_decimal(reconstructed_digits, len(raw), zero_prefix)
    bytes_time = time.perf_counter() - t4

    total_decode_time = unrank_time + bytes_time
    ok = reconstructed_bytes == raw and hashlib.sha256(reconstructed_bytes).hexdigest() == raw_hash

    print("\nDecode")
    print(f"  Address materialisation: {unrank_time:.2f}s")
    print(f"  Decimal -> bytes: {bytes_time:.2f}s")
    print(f"  Total decode time: {total_decode_time:.2f}s")
    print(f"  Verify: {'BIT-PERFECT' if ok else 'FAILED'}")
    return ok


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Benchmark whole-file exact scalar-address recipe")
    parser.add_argument("file", help="Whole file to benchmark")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    return 0 if run_benchmark(Path(args.file).expanduser()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
