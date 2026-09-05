#!/usr/bin/env python3
"""
RIDE V8 - TSP-guided constrained family registry.

Adds a second decoder-known family between tiny shared generators and the
full-rank fallback:

  FAMILY_PCG32       : shared global Fisher-Yates family
  FAMILY_BLOCK_LOCAL : TSP-guided local block family
  FAMILY_FULL_RANK   : exact generic fallback

The new block family is a real address family, not a target-specific map:
the decoder knows the rule:
  - rebuild the sorted base from coords
  - split into deterministic blocks of size B
  - unrank each block independently using the block-local address stream

The encoder uses thermo/cycle spans to choose candidate block sizes and only
emits this family when it exactly materialises the target and beats fallback.
"""

from __future__ import annotations

import hashlib
import math
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


def decode_uvarint(data: bytes, offset: int) -> tuple[int, int]:
    shift = 0
    value = 0
    while True:
        byte = data[offset]
        offset += 1
        value |= (byte & 0x7F) << shift
        if not (byte & 0x80):
            return value, offset
        shift += 7


def decode_svarint(data: bytes, offset: int) -> tuple[int, int]:
    raw, offset = decode_uvarint(data, offset)
    return (raw >> 1) ^ -(raw & 1), offset


FAMILY_PCG32 = 1
FAMILY_BLOCK_LOCAL = 2
FAMILY_FULL_RANK = 255


def digit_hash(digits: list[int]) -> str:
    return hashlib.sha256("".join(str(d) for d in digits).encode()).hexdigest()


def build_base_from_freq(freq: list[int]) -> list[int]:
    base: list[int] = []
    for digit, count in enumerate(freq):
        base.extend([digit] * count)
    return base


def try_pcg32_family(target_digits: list[int], max_seed: int = 200_000) -> tuple[int, dict] | None:
    base = build_base_from_freq(count_digits(target_digits))
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
                "family": "pcg32_seed",
                "seeds_scanned": seed + 1,
                "constraint_passes": constraint_passes,
                "search_time_s": time.time() - t0,
                "constraints": len(constraints),
            }
    return None


def candidate_block_sizes(target_digits: list[int], base: list[int]) -> list[int]:
    """
    TSP-guided candidate scales from cycle spans.
    Small spans suggest a local family should work well.
    """
    thermo = thermo_analyse(target_digits, base)
    perm = thermo["perm"]

    spans = [abs(i - perm[i]) for i in range(len(perm)) if i != perm[i]]
    if not spans:
        return [8, 16, 32]

    mean_span = max(1, sum(spans) // len(spans))
    max_span = max(spans)

    raw = {
        8,
        16,
        32,
        64,
        128,
        256,
        512,
        1024,
        1 << max(0, int(math.log2(mean_span))),
        1 << max(0, int(math.log2(max_span))),
        1 << max(0, int(math.log2(max(1, mean_span // 2)))),
        1 << max(0, int(math.log2(max(1, max_span // 2)))),
    }
    n = len(target_digits)
    result = sorted(b for b in raw if 2 <= b <= n)
    return result


def split_blocks(seq: list[int], block_size: int) -> list[list[int]]:
    return [seq[i:i + block_size] for i in range(0, len(seq), block_size)]


def pack_block_local_address(block_size: int, ranks: list[int]) -> bytes:
    out = bytearray()
    out.extend(encode_uvarint(block_size))
    out.extend(encode_uvarint(len(ranks)))
    for rank in ranks:
        out.extend(encode_uvarint(rank))
    return bytes(out)


def unpack_block_local_address(data: bytes) -> tuple[int, list[int]]:
    offset = 0
    block_size, offset = decode_uvarint(data, offset)
    n_blocks, offset = decode_uvarint(data, offset)
    ranks: list[int] = []
    for _ in range(n_blocks):
        rank, offset = decode_uvarint(data, offset)
        ranks.append(rank)
    if offset != len(data):
        raise ValueError("trailing bytes in block-local address")
    return block_size, ranks


def try_block_local_family(target_digits: list[int]) -> tuple[bytes, dict] | None:
    """
    Exact block-local family:
      - base is deterministic from coords
      - split both target and base into same block boundaries
      - each target block must be a permutation of the corresponding base block
      - address stores local block ranks only
    """
    freq = count_digits(target_digits)
    base = build_base_from_freq(freq)
    candidates = candidate_block_sizes(target_digits, base)
    best: tuple[bytes, dict] | None = None

    for block_size in candidates:
        base_blocks = split_blocks(base, block_size)
        target_blocks = split_blocks(target_digits, block_size)
        if len(base_blocks) != len(target_blocks):
            continue

        ranks: list[int] = []
        ok = True
        for base_block, target_block in zip(base_blocks, target_blocks):
            block_freq = count_digits(target_block)
            if block_freq != count_digits(base_block):
                ok = False
                break
            ranks.append(rank_permutation_fast(target_block, block_freq))

        if not ok:
            continue

        address = pack_block_local_address(block_size, ranks)
        meta = {
            "family": "block_local",
            "block_size": block_size,
            "blocks": len(ranks),
            "address_bytes": len(address),
        }
        if best is None or len(address) < len(best[0]):
            best = (address, meta)

    return best


def decode_block_local_digits(freq: list[int], address: bytes) -> list[int]:
    base = build_base_from_freq(freq)
    block_size, ranks = unpack_block_local_address(address)
    base_blocks = split_blocks(base, block_size)
    if len(base_blocks) != len(ranks):
        raise ValueError("block-local address count mismatch")

    out: list[int] = []
    for base_block, rank in zip(base_blocks, ranks):
        block_freq = count_digits(base_block)
        out.extend(unrank_permutation_fast(rank, block_freq, len(base_block)))
    return out


def full_rank_address(target_digits: list[int]) -> tuple[int, int]:
    freq = count_digits(target_digits)
    addr = rank_permutation_fast(target_digits, freq)
    bits = max(1, addr.bit_length())
    return addr, (bits + 7) // 8


def encode_digits(target_digits: list[int], max_seed: int = 200_000, verbose: bool = True) -> dict:
    t0 = time.time()
    freq = count_digits(target_digits)
    coords = encode_frequency_coords(freq)
    digest = digit_hash(target_digits)
    coord_bytes = coords_payload_bytes(coords)

    # Candidate 1: shared PCG family
    pcg = try_pcg32_family(target_digits, max_seed=max_seed)
    best_packet = None
    best_bytes = None

    if pcg is not None:
        seed, meta = pcg
        addr_bytes = max(1, (int(seed).bit_length() + 7) // 8)
        packet = {"V": 8, "COORDS": coords, "FAM": FAMILY_PCG32, "ADDR": seed, "H": digest}
        size = 1 + coord_bytes + 1 + addr_bytes + 32
        best_packet = (packet, meta, size)
        best_bytes = size

    # Candidate 2: TSP-guided block family
    block = try_block_local_family(target_digits)
    if block is not None:
        address, meta = block
        size = 1 + coord_bytes + 1 + len(address) + 32
        if best_bytes is None or size < best_bytes:
            packet = {"V": 8, "COORDS": coords, "FAM": FAMILY_BLOCK_LOCAL, "ADDR": address, "H": digest}
            best_packet = (packet, meta, size)
            best_bytes = size

    # Candidate 3: exact full-rank fallback
    full_addr, full_addr_bytes = full_rank_address(target_digits)
    full_size = 1 + coord_bytes + 1 + full_addr_bytes + 32
    if best_bytes is None or full_size < best_bytes:
        best_packet = (
            {"V": 8, "COORDS": coords, "FAM": FAMILY_FULL_RANK, "ADDR": full_addr, "H": digest},
            {"family": "full_rank", "address_bytes": full_addr_bytes},
            full_size,
        )

    packet, meta, packet_size = best_packet
    elapsed = time.time() - t0

    if verbose:
        print(f"  ENCODE DIGITS: {len(target_digits):,} digits")
        print(f"    Family: {meta['family']}")
        if meta["family"] == "pcg32_seed":
            print(
                f"    Addr: seed={packet['ADDR']:,}, "
                f"scanned={meta['seeds_scanned']:,}, "
                f"constraint_passes={meta['constraint_passes']:,}"
            )
        elif meta["family"] == "block_local":
            print(
                f"    Addr: block_size={meta['block_size']}, "
                f"blocks={meta['blocks']}, "
                f"bytes={meta['address_bytes']}"
            )
        else:
            print(f"    Addr: full-rank bytes={meta['address_bytes']}")
        print(f"    Packet: ~{packet_size:,} bytes")
        print(f"    Time: {elapsed:.3f}s")

    return packet


def decode_digits(packet: dict, verbose: bool = True) -> list[int] | None:
    t0 = time.time()
    freq = decode_frequency_coords(packet["COORDS"])
    family = int(packet["FAM"])

    if family == FAMILY_PCG32:
        digits = fisher_yates(build_base_from_freq(freq), int(packet["ADDR"]))
        family_name = "pcg32_seed"
    elif family == FAMILY_BLOCK_LOCAL:
        digits = decode_block_local_digits(freq, packet["ADDR"])
        family_name = "block_local"
    elif family == FAMILY_FULL_RANK:
        digits = unrank_permutation_fast(int(packet["ADDR"]), freq, sum(freq))
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
    addr = packet["ADDR"]
    if isinstance(addr, bytes):
        addr_bytes = len(addr)
    else:
        addr_bytes = max(1, (int(addr).bit_length() + 7) // 8)
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
    print("║  RIDE V8 - TSP-GUIDED FAMILY REGISTRY                       ║")
    print("║  Shared families + local constrained family + exact fallback║")
    print("╚══════════════════════════════════════════════════════════════╝")

    total = 0
    passed = 0

    # Exact PCG family hits
    for seed, n_digits in [(42, 300), (4096, 3000)]:
        base = []
        for digit in range(10):
            base.extend([digit] * (n_digits // 10))
        digits = fisher_yates(base, seed)
        total += 1
        if run_digit_case(f"PCG family exact hit seed={seed}", digits, max_seed=seed + 100):
            passed += 1

    # Exact block-local family hit: local shuffles within deterministic blocks.
    # Use a block size that crosses digit boundaries in the sorted base so the
    # constrained family is genuinely exercised.
    block_base = []
    for digit in range(10):
        block_base.extend([digit] * 64)
    block_digits = []
    block_size = 128
    for i in range(0, len(block_base), block_size):
        block = list(block_base[i:i + block_size])
        block_digits.extend(fisher_yates(block, i + 17))
    total += 1
    if run_digit_case("Block-local family exact hit", block_digits, max_seed=20_000):
        passed += 1

    # Real-ish fallback cases
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
