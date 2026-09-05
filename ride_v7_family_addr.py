#!/usr/bin/env python3
"""
RIDE V7 - Family address registry.

The decoder contains a shared dictionary of permutation families.
The encoder does the hard work of finding which family/address exactly
materialises the target.

Current families:
  - pcg32_seed : tiny 64-bit-style address if the target lies in the shared
                 Fisher-Yates family.
  - full_rank  : exact fallback deterministic address from V6.

This is the architecture bridge toward the smaller TSP-guided family:
the packet now carries {coords, family, address, hash}, and the decoder
already knows how to interpret the address based on the family id.
"""

from __future__ import annotations

import hashlib
import os
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
MIAI = Path("/Users/trentpalelei/MIAI")
for candidate in (HERE, MIAI):
    candidate_str = str(candidate)
    if candidate.exists() and candidate_str not in sys.path:
        sys.path.insert(0, candidate_str)

from ride_v1_thermo_encoder import fisher_yates, fisher_yates_full_with_check, thermo_analyse
from ride_v6_kcoords_addr import (
    bytes_to_digits,
    digits_to_bytes,
    count_digits,
    encode_frequency_coords,
    decode_frequency_coords,
    coords_payload_bytes,
    rank_permutation_fast,
    unrank_permutation_fast,
    encode_uvarint,
)


FAMILY_PCG32 = 1
FAMILY_FULL_RANK = 255


def build_base_from_digits(digits: list[int]) -> list[int]:
    freq = count_digits(digits)
    base: list[int] = []
    for digit, count in enumerate(freq):
        base.extend([digit] * count)
    return base


def digit_hash(digits: list[int]) -> str:
    return hashlib.sha256("".join(str(d) for d in digits).encode()).hexdigest()


def try_pcg32_family(target_digits: list[int], max_seed: int = 200_000) -> tuple[int, dict] | None:
    """
    Try to express the target as:
      target = fisher_yates(sorted_multiset(target), seed)

    The decoder already knows this family, so the packet only needs the seed.
    """
    base = build_base_from_digits(target_digits)
    thermo = thermo_analyse(target_digits, base)
    constraints = thermo["constraints"]
    expected_hash = digit_hash(target_digits)

    t0 = time.time()
    constraint_passes = 0

    for seed in range(max_seed):
        candidate = fisher_yates_full_with_check(base, seed, constraints)
        if candidate is None:
            continue
        constraint_passes += 1
        if digit_hash(candidate) == expected_hash:
            return seed, {
                "search_time_s": time.time() - t0,
                "seeds_scanned": seed + 1,
                "constraint_passes": constraint_passes,
                "distance": thermo["n_steps"],
                "constraints": len(constraints),
            }

    return None


def encode_digits(target_digits: list[int], max_seed: int = 200_000, verbose: bool = True) -> dict:
    t0 = time.time()
    freq = count_digits(target_digits)
    coords = encode_frequency_coords(freq)
    digest = digit_hash(target_digits)

    pcg = try_pcg32_family(target_digits, max_seed=max_seed)
    if pcg is not None:
        addr, meta = pcg
        packet = {
            "V": 7,
            "COORDS": coords,
            "FAM": FAMILY_PCG32,
            "ADDR": addr,
            "H": digest,
        }
        elapsed = time.time() - t0
        if verbose:
            coord_bytes = coords_payload_bytes(coords)
            addr_bytes = max(1, (int(addr).bit_length() + 7) // 8)
            total_bytes = 1 + coord_bytes + 1 + addr_bytes + 32
            print(f"  ENCODE DIGITS: {len(target_digits):,} digits")
            print(f"    Family: pcg32_seed")
            print(f"    Addr: seed={addr:,} ({addr_bytes} bytes)")
            print(
                f"    Search: scanned={meta['seeds_scanned']:,}, "
                f"constraint_passes={meta['constraint_passes']:,}, "
                f"constraints={meta['constraints']}"
            )
            print(f"    Packet: ~{total_bytes:,} bytes")
            print(f"    Time: {elapsed:.3f}s")
        return packet

    addr = rank_permutation_fast(target_digits, freq)
    packet = {
        "V": 7,
        "COORDS": coords,
        "FAM": FAMILY_FULL_RANK,
        "ADDR": addr,
        "H": digest,
    }
    elapsed = time.time() - t0
    if verbose:
        coord_bytes = coords_payload_bytes(coords)
        addr_bits = max(1, int(addr).bit_length())
        addr_bytes = (addr_bits + 7) // 8
        total_bytes = 1 + coord_bytes + 1 + addr_bytes + 32
        print(f"  ENCODE DIGITS: {len(target_digits):,} digits")
        print(f"    Family: full_rank fallback")
        print(f"    Addr: {addr_bits:,} bits = {addr_bytes:,} bytes")
        print(f"    Packet: ~{total_bytes:,} bytes")
        print(f"    Time: {elapsed:.3f}s")
    return packet


def decode_digits(packet: dict, verbose: bool = True) -> list[int] | None:
    t0 = time.time()
    freq = decode_frequency_coords(packet["COORDS"])
    family = int(packet["FAM"])
    addr = int(packet["ADDR"])

    if family == FAMILY_PCG32:
        base: list[int] = []
        for digit, count in enumerate(freq):
            base.extend([digit] * count)
        digits = fisher_yates(base, addr)
        family_name = "pcg32_seed"
    elif family == FAMILY_FULL_RANK:
        digits = unrank_permutation_fast(addr, freq, sum(freq))
        family_name = "full_rank"
    else:
        raise ValueError(f"unknown family id: {family}")

    ok = digit_hash(digits) == packet["H"]
    elapsed = time.time() - t0
    if verbose:
        print(f"  DECODE DIGITS: family={family_name}")
        print(f"    Hash: {'OK' if ok else 'MISMATCH'}")
        print(f"    Time: {elapsed:.3f}s")
    return digits if ok else None


def encode_bytes(data: bytes, max_seed: int = 200_000, verbose: bool = True) -> dict:
    return encode_digits(bytes_to_digits(data), max_seed=max_seed, verbose=verbose)


def decode_bytes(packet: dict, verbose: bool = True) -> bytes | None:
    digits = decode_digits(packet, verbose=verbose)
    if digits is None:
        return None
    return digits_to_bytes(digits)


def packet_bytes(packet: dict) -> int:
    coord_bytes = coords_payload_bytes(packet["COORDS"])
    addr = int(packet["ADDR"])
    addr_bytes = max(1, (addr.bit_length() + 7) // 8)
    return 1 + coord_bytes + 1 + addr_bytes + 32


def run_digit_case(name: str, digits: list[int], max_seed: int) -> bool:
    print(f"\n{'=' * 72}")
    print(f"  {name}")
    print(f"  Input: {len(digits):,} digits")
    print(f"{'=' * 72}")
    packet = encode_digits(digits, max_seed=max_seed, verbose=True)
    result = decode_digits(packet, verbose=True)
    ok = result == digits
    print(f"  Packet bytes: ~{packet_bytes(packet):,}")
    print(f"  Verify: {'BIT-PERFECT' if ok else 'FAILED'}")
    return ok


def run_byte_case(name: str, data: bytes, max_seed: int) -> bool:
    print(f"\n{'=' * 72}")
    print(f"  {name}")
    print(f"  Input: {len(data):,} bytes")
    print(f"{'=' * 72}")
    packet = encode_bytes(data, max_seed=max_seed, verbose=True)
    result = decode_bytes(packet, verbose=True)
    ok = result == data
    print(f"  Packet bytes: ~{packet_bytes(packet):,}")
    print(f"  Verify: {'BIT-PERFECT' if ok else 'FAILED'}")
    return ok


if __name__ == "__main__":
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V7 - FAMILY ADDRESS REGISTRY                          ║")
    print("║  Decoder-owned address dictionary with exact fallback       ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    total = 0
    passed = 0

    # Positive family-hit cases: generated exactly by the shared PCG32 family.
    for seed, n_digits in [(42, 300), (777, 600), (4096, 3000)]:
        base = []
        for digit in range(10):
            base.extend([digit] * (n_digits // 10))
        digits = fisher_yates(base, seed)
        total += 1
        if run_digit_case(f"PCG family exact hit seed={seed}", digits, max_seed=seed + 100):
            passed += 1

    # Real byte data: likely fallback today, but exact decode should still work.
    total += 1
    if run_byte_case("Random 512B", os.urandom(512), max_seed=20_000):
        passed += 1

    real_file = "/Users/trentpalelei/Downloads/d345a5ca-975d-4a25-a4ca-59cf532e0792.jpeg"
    if os.path.exists(real_file):
        with open(real_file, "rb") as handle:
            jpeg_slice = handle.read(1024)
        total += 1
        if run_byte_case("Real JPEG slice 1KB", jpeg_slice, max_seed=20_000):
            passed += 1

    print(f"\n{'=' * 72}")
    print(f"  SUMMARY: {passed}/{total} cases passed")
    print(f"{'=' * 72}")
