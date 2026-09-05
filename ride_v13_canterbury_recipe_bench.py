#!/usr/bin/env python3
"""
RIDE V13 - Whole-file recipe benchmark.

Exact benchmark around the corrected pipeline:
  1. file -> one lossless decimal number
  2. actual thermodynamic K constant source
  3. deterministic frequency delta to match the file's multiset
  4. exact permutation payload
  5. raw-byte hash verification

This is not the final tiny recipe. It is the honest exact benchmark for the
current architecture so we can answer:
  - can we materialise the full Canterbury zip?
  - what does the recipe cost today?
  - how long does encode/decode take?
"""

from __future__ import annotations

import argparse
import hashlib
import math
import sys
import time
from array import array
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


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(10_000_000)


def encode_uvarint(value: int) -> bytes:
    if value < 0:
        raise ValueError("uvarint cannot encode negative values")
    out = bytearray()
    while value >= 0x80:
        out.append((value & 0x7F) | 0x80)
        value >>= 7
    out.append(value)
    return bytes(out)


def zigzag_encode(value: int) -> int:
    return (value << 1) ^ (value >> 63) if value < 0 else value << 1


def encode_svarint(value: int) -> bytes:
    return encode_uvarint(zigzag_encode(value))


def str_to_digits(s: str) -> bytearray:
    return bytearray(ch - 48 for ch in s.encode())


def digits_to_decimal_string(digits: bytearray) -> str:
    return bytes(d + 48 for d in digits).decode()


def leading_zero_bytes(data: bytes) -> int:
    index = 0
    size = len(data)
    while index < size and data[index] == 0:
        index += 1
    return index


def deterministic_frequency_patch(source_digits: bytearray, target_counts: list[int]) -> tuple[bytearray, list[int], int]:
    """
    Deterministically patch the K constant to the file's exact digit multiset.

    Rule:
      - scan source left-to-right
      - whenever a digit has surplus, rewrite that position to the next deficit digit
      - deficit digits are emitted in ascending order
    """
    source_counts = [0] * 10
    for digit in source_digits:
        source_counts[digit] += 1

    delta = [target_counts[d] - source_counts[d] for d in range(10)]
    deficits: list[int] = []
    for digit in range(10):
        if delta[digit] > 0:
            deficits.extend([digit] * delta[digit])

    surplus_remaining = [max(0, -value) for value in delta]
    patched = bytearray(source_digits)
    deficit_index = 0

    for position, digit in enumerate(source_digits):
        if surplus_remaining[digit] <= 0:
            continue
        patched[position] = deficits[deficit_index]
        surplus_remaining[digit] -= 1
        deficit_index += 1

    if deficit_index != len(deficits):
        raise ValueError("deterministic patch did not consume all deficits")

    patched_counts = [0] * 10
    for digit in patched:
        patched_counts[digit] += 1
    if patched_counts != target_counts:
        raise ValueError("patched source does not match target multiset")

    edits = sum(max(0, value) for value in delta)
    return patched, delta, edits


def build_perm_target_to_source(target_digits: bytearray, source_digits: bytearray) -> array:
    """
    Build exact mapping perm where target[i] = source[perm[i]].

    Matching rule is fixed-point maximising for repeated digits.
    """
    n = len(target_digits)
    target_pos = [array("I") for _ in range(10)]
    source_pos = [array("I") for _ in range(10)]

    for index, digit in enumerate(target_digits):
        target_pos[digit].append(index)
    for index, digit in enumerate(source_digits):
        source_pos[digit].append(index)

    perm = array("I", [0]) * n

    for digit in range(10):
        tgt = target_pos[digit]
        src = source_pos[digit]
        t_len = len(tgt)
        s_len = len(src)
        t_i = 0
        s_i = 0
        rem_t = array("I")
        rem_s = array("I")

        while t_i < t_len and s_i < s_len:
            t_pos = tgt[t_i]
            s_pos = src[s_i]
            if t_pos == s_pos:
                perm[t_pos] = t_pos
                t_i += 1
                s_i += 1
            elif t_pos < s_pos:
                rem_t.append(t_pos)
                t_i += 1
            else:
                rem_s.append(s_pos)
                s_i += 1

        while t_i < t_len:
            rem_t.append(tgt[t_i])
            t_i += 1
        while s_i < s_len:
            rem_s.append(src[s_i])
            s_i += 1

        for t_pos, s_pos in zip(rem_t, rem_s):
            perm[t_pos] = s_pos

    return perm


def permutation_cycle_mile(perm: array) -> tuple[int, int]:
    visited = bytearray(len(perm))
    cycles = 0
    for index in range(len(perm)):
        if visited[index]:
            continue
        cycles += 1
        current = index
        while not visited[current]:
            visited[current] = 1
            current = perm[current]
    return len(perm) - cycles, cycles


def apply_perm(source_digits: bytearray, perm: array) -> bytearray:
    out = bytearray(len(perm))
    for target_index, source_index in enumerate(perm):
        out[target_index] = source_digits[source_index]
    return out


def materialize_bytes_from_decimal(decimal_digits: bytearray, byte_length: int, leading_zeros: int) -> bytes:
    decimal_str = digits_to_decimal_string(decimal_digits)
    body_len = byte_length - leading_zeros
    body = int(decimal_str).to_bytes(body_len, "big") if body_len > 0 else b""
    return (b"\0" * leading_zeros) + body


def packet_size_bytes(params: tuple[int, int, int, int], delta: list[int], perm: array, raw_length: int, leading_zeros: int) -> dict[str, int]:
    k_bytes = sum(len(encode_uvarint(value)) for value in params)
    delta_bytes = sum(len(encode_svarint(value)) for value in delta)
    meta_bytes = len(encode_uvarint(raw_length)) + len(encode_uvarint(leading_zeros))
    width = max(1, (len(perm) - 1).bit_length() + 7) // 8
    width = max(1, width)
    perm_bytes = 1 + len(encode_uvarint(len(perm))) + len(perm) * width
    hash_bytes = 32
    total = k_bytes + delta_bytes + meta_bytes + perm_bytes + hash_bytes
    return {
        "k_bytes": k_bytes,
        "delta_bytes": delta_bytes,
        "meta_bytes": meta_bytes,
        "perm_bytes": perm_bytes,
        "hash_bytes": hash_bytes,
        "total_bytes": total,
        "perm_width": width,
    }


def run_benchmark(path: Path) -> bool:
    raw = path.read_bytes()
    raw_hash = hashlib.sha256(raw).hexdigest()
    zero_prefix = leading_zero_bytes(raw)

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V13 - WHOLE-FILE RECIPE BENCHMARK                     ║")
    print("║  actual K + delta + exact permutation payload               ║")
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
    k_time = time.perf_counter() - t1

    t2 = time.perf_counter()
    patched_source, delta, edits = deterministic_frequency_patch(k_digits, target_counts)
    patch_time = time.perf_counter() - t2

    t3 = time.perf_counter()
    perm = build_perm_target_to_source(target_digits, patched_source)
    perm_time = time.perf_counter() - t3

    t4 = time.perf_counter()
    mile, cycles = permutation_cycle_mile(perm)
    cycle_time = time.perf_counter() - t4

    encode_time = decimal_time + k_time + patch_time + perm_time + cycle_time

    size = packet_size_bytes((v0, a, b, v9), delta, perm, len(raw), zero_prefix)

    print("\nEncode")
    print(f"  Actual K params: v0={v0:,} a={a:,} b={b:,} v9={v9:,}")
    print(f"  Actual K materialization: {k_time:.2f}s  ({steps} Kaprekar steps)")
    print(f"  Frequency delta L1: {l1:,}")
    print(f"  Deterministic patch edits: {edits:,} digits")
    print(f"  Patch time: {patch_time:.2f}s")
    print(f"  Permutation build: {perm_time:.2f}s")
    print(f"  Mile: {mile:,}  cycles: {cycles:,}")
    print(f"  Mile analysis time: {cycle_time:.2f}s")
    print(f"  Total encode time: {encode_time:.2f}s")

    print("\nPacket")
    print(f"  K params: {size['k_bytes']:,}B")
    print(f"  Delta: {size['delta_bytes']:,}B")
    print(f"  Meta: {size['meta_bytes']:,}B")
    print(f"  Perm payload: {size['perm_bytes']:,}B  (width={size['perm_width']}B)")
    print(f"  SHA-256: {size['hash_bytes']:,}B")
    print(f"  Total recipe: {size['total_bytes']:,}B")
    print(f"  Raw/recipe ratio: {len(raw) / size['total_bytes']:.3f}x")

    t5 = time.perf_counter()
    reconstructed_digits = apply_perm(patched_source, perm)
    perm_decode_time = time.perf_counter() - t5

    t6 = time.perf_counter()
    reconstructed_bytes = materialize_bytes_from_decimal(reconstructed_digits, len(raw), zero_prefix)
    bytes_decode_time = time.perf_counter() - t6

    total_decode_time = perm_decode_time + bytes_decode_time
    ok = reconstructed_bytes == raw and hashlib.sha256(reconstructed_bytes).hexdigest() == raw_hash

    print("\nDecode")
    print(f"  Permutation replay: {perm_decode_time:.2f}s")
    print(f"  Decimal -> bytes: {bytes_decode_time:.2f}s")
    print(f"  Total decode time: {total_decode_time:.2f}s")
    print(f"  Verify: {'BIT-PERFECT' if ok else 'FAILED'}")
    return ok


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Benchmark whole-file recipe cost")
    parser.add_argument("file", help="Whole file to benchmark")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    ok = run_benchmark(Path(args.file).expanduser())
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
