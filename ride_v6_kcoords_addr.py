#!/usr/bin/env python3
"""
RIDE V6 - Exact coords + deterministic permutation address.

This unifies the two pieces that now work:
  1. Exact coordinate-only content reconstruction (from V5)
  2. Direct deterministic materialisation by permutation address (from V3)

Packet:
  {
    V: 6,
    COORDS: {
      N: total digit count,
      K: [k1, k2, k3],
      A: [f0, f1, f2, f3, f4, f5],
    },
    ADDR: multiset permutation rank of the digit stream,
    H: sha256(digit_string),
  }

The encoder does the expensive ranking step. The decoder reconstructs the
digit frequency vector from coords, then un-ranks directly to materialise
the exact digit stream with no search and no path replay.
"""

from __future__ import annotations

import hashlib
import math
import os
import time


E1 = [+1, 0, -1, +1, 0, 0, +1, -1, 0, -1]
E2 = [0, +1, +1, -3, +1, +1, -3, +1, +1, 0]
E3 = [-1, 0, +1, 0, -1, -1, 0, +1, 0, +1]

TAIL_INV = (
    (0, 1, 0, 1),
    (-1, 4, 1, 5),
    (1, -1, 0, -2),
    (1, -4, -1, -4),
)


def bytes_to_digits(data: bytes) -> list[int]:
    digits: list[int] = []
    for value in data:
        digits.append((value // 100) % 10)
        digits.append((value // 10) % 10)
        digits.append(value % 10)
    return digits


def digits_to_bytes(digits: list[int]) -> bytes:
    out = bytearray()
    for i in range(0, len(digits), 3):
        out.append(digits[i] * 100 + digits[i + 1] * 10 + digits[i + 2])
    return bytes(out)


def count_digits(digits: list[int]) -> list[int]:
    freq = [0] * 10
    for digit in digits:
        freq[digit] += 1
    return freq


def compute_k_moments(freq: list[int]) -> tuple[int, int, int]:
    return (
        sum(E1[i] * freq[i] for i in range(10)),
        sum(E2[i] * freq[i] for i in range(10)),
        sum(E3[i] * freq[i] for i in range(10)),
    )


def encode_frequency_coords(freq: list[int]) -> dict:
    k1, k2, k3 = compute_k_moments(freq)
    return {"N": sum(freq), "K": [k1, k2, k3], "A": list(freq[:6])}


def decode_frequency_coords(coords: dict) -> list[int]:
    n = int(coords["N"])
    k1, k2, k3 = [int(v) for v in coords["K"]]
    anchors = [int(v) for v in coords["A"]]
    rhs = [
        n - sum(anchors),
        k1 - sum(E1[i] * anchors[i] for i in range(6)),
        k2 - sum(E2[i] * anchors[i] for i in range(6)),
        k3 - sum(E3[i] * anchors[i] for i in range(6)),
    ]
    tail = [sum(row[j] * rhs[j] for j in range(4)) for row in TAIL_INV]
    freq = anchors + tail
    if any(value < 0 for value in freq):
        raise ValueError(f"decoded negative frequency vector: {freq}")
    if sum(freq) != n or list(compute_k_moments(freq)) != [k1, k2, k3]:
        raise ValueError("coordinate decode failed validation")
    return freq


def zigzag_encode(value: int) -> int:
    return (value << 1) ^ (value >> 63) if value < 0 else value << 1


def encode_uvarint(value: int) -> bytes:
    if value < 0:
        raise ValueError("uvarint cannot encode negative values")
    out = bytearray()
    while value >= 0x80:
        out.append((value & 0x7F) | 0x80)
        value >>= 7
    out.append(value)
    return bytes(out)


def encode_svarint(value: int) -> bytes:
    return encode_uvarint(zigzag_encode(value))


def coords_payload_bytes(coords: dict) -> int:
    size = len(encode_uvarint(int(coords["N"])))
    size += sum(len(encode_svarint(int(value))) for value in coords["K"])
    size += sum(len(encode_uvarint(int(value))) for value in coords["A"])
    return size


def multinomial(total: int, freq: list[int]) -> int:
    """
    Exact count:
      total! / (f0! * ... * f9!)
    """
    result = 1
    remaining = total
    for count in freq:
        for k in range(1, count + 1):
            result = result * remaining // k
            remaining -= 1
    return result


def rank_permutation_fast(perm: list[int], freq: list[int]) -> int:
    f = list(freq)
    total = len(perm)
    perms = multinomial(total, f)
    rank = 0

    for digit in perm:
        for smaller in range(digit):
            if f[smaller] > 0:
                rank += perms * f[smaller] // total

        perms = perms * f[digit] // total
        f[digit] -= 1
        total -= 1
        if total == 0:
            break

    return rank


def unrank_permutation_fast(rank: int, freq: list[int], total: int) -> list[int]:
    f = list(freq)
    perms = multinomial(total, f)
    result: list[int] = []

    while total:
        for digit in range(10):
            if f[digit] == 0:
                continue
            count = perms * f[digit] // total
            if rank < count:
                result.append(digit)
                perms = count
                f[digit] -= 1
                total -= 1
                break
            rank -= count

    return result


def encode(data: bytes, verbose: bool = True) -> dict:
    t0 = time.time()

    digits = bytes_to_digits(data)
    freq = count_digits(digits)
    coords = encode_frequency_coords(freq)
    addr = rank_permutation_fast(digits, freq)
    digest = hashlib.sha256("".join(str(d) for d in digits).encode()).hexdigest()

    packet = {"V": 6, "COORDS": coords, "ADDR": addr, "H": digest}

    elapsed = time.time() - t0
    if verbose:
        coord_bytes = coords_payload_bytes(coords)
        addr_bits = max(1, addr.bit_length())
        addr_bytes = (addr_bits + 7) // 8
        total_bytes = 1 + coord_bytes + addr_bytes + 32
        print(f"  ENCODE: {len(data):,} bytes = {len(digits):,} digits")
        print(f"    Coords: {coord_bytes} bytes")
        print(f"    Addr: {addr_bits:,} bits = {addr_bytes:,} bytes")
        print(f"    Packet: ~{total_bytes:,} bytes")
        print(f"    Time: {elapsed:.3f}s")

    return packet


def decode(packet: dict, verbose: bool = True) -> bytes | None:
    t0 = time.time()

    freq = decode_frequency_coords(packet["COORDS"])
    total = sum(freq)
    digits = unrank_permutation_fast(int(packet["ADDR"]), freq, total)
    digest = hashlib.sha256("".join(str(d) for d in digits).encode()).hexdigest()
    ok = digest == packet["H"]
    elapsed = time.time() - t0

    if verbose:
        print(f"  DECODE: {total:,} digits")
        print(f"    Hash: {'OK' if ok else 'MISMATCH'}")
        print(f"    Time: {elapsed:.3f}s")

    if not ok:
        return None
    return digits_to_bytes(digits)


def run_case(name: str, data: bytes) -> bool:
    from ride_v5_kcoords_path import encode as encode_v5

    print(f"\n{'=' * 72}")
    print(f"  {name}")
    print(f"  Input: {len(data):,} bytes")
    print(f"{'=' * 72}")

    packet = encode(data, verbose=True)
    result = decode(packet, verbose=True)
    ok = result == data

    coord_bytes = coords_payload_bytes(packet["COORDS"])
    addr_bits = max(1, int(packet["ADDR"]).bit_length())
    addr_bytes = (addr_bits + 7) // 8
    total_v6 = 1 + coord_bytes + addr_bytes + 32

    packet_v5 = encode_v5(data, verbose=False)
    total_v5 = 1 + coords_payload_bytes(packet_v5["COORDS"]) + len(packet_v5["PATH"]) + 32

    print(f"  Packet comparison: v5 path ~{total_v5:,} bytes vs v6 addr ~{total_v6:,} bytes")
    print(f"  Verify: {'BIT-PERFECT' if ok else 'FAILED'}")
    return ok


if __name__ == "__main__":
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V6 - EXACT COORDS + DETERMINISTIC ADDRESS             ║")
    print("║  Coordinate-only content, direct unranking materialisation  ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    cases: list[tuple[str, bytes]] = [
        ("Hello payload", b"Hello deterministic address"),
        ("Repeated pattern", bytes([10, 20, 30, 40, 50] * 40)),
        ("Random 256B", os.urandom(256)),
        ("Random 1KB", os.urandom(1024)),
    ]

    real_file = "/Users/trentpalelei/Downloads/d345a5ca-975d-4a25-a4ca-59cf532e0792.jpeg"
    if os.path.exists(real_file):
        with open(real_file, "rb") as handle:
            cases.append(("Real JPEG slice 1KB", handle.read(1024)))

    total = 0
    passed = 0
    for name, data in cases:
        total += 1
        if run_case(name, data):
            passed += 1

    print(f"\n{'=' * 72}")
    print(f"  SUMMARY: {passed}/{total} cases passed")
    print(f"{'=' * 72}")
