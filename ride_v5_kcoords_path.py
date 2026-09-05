#!/usr/bin/env python3
"""
RIDE V5 - Exact K-coordinate content + deterministic path replay.

This version fixes the main gap in the earlier MIAI prototypes:
the decoder can reconstruct the full digit-frequency vector from coordinates
alone, without falling back to a raw frequency table.

Packet shape:
  {
    V: 5,
    COORDS: {
      N: total digit count,
      K: [k1, k2, k3],   # Kaprekar moments
      A: [f0, f1, f2, f3, f4, f5],  # anchor coordinates
    },
    D: minimum transposition distance from the base sequence,
    PATH: delta-encoded cycle path,
    H: sha256(digit_string),
  }

Notes:
  - This is an exact coordinate-only content layer.
  - The ordering layer is still a replayable cycle path, not yet the final
    tiny TSP-style shortcut number.
  - The decoder is fully deterministic and does not need the base sequence
    or raw frequency vector sent through the packet.
"""

from __future__ import annotations

import hashlib
import os
import time
from collections import defaultdict
from typing import Iterable


# Kaprekar basis moments used by the existing RIDE experiments.
E1 = [+1, 0, -1, +1, 0, 0, +1, -1, 0, -1]
E2 = [0, +1, +1, -3, +1, +1, -3, +1, +1, 0]
E3 = [-1, 0, +1, 0, -1, -1, 0, +1, 0, +1]

# We store digits 0..5 directly and solve 6..9 from:
#   sum(F) = N
#   dot(E1, F) = k1
#   dot(E2, F) = k2
#   dot(E3, F) = k3
#
# The 4x4 tail system for digits 6,7,8,9 has determinant 1, so the inverse
# is integer-valued and exact.
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


def build_base_sequence(freq: list[int]) -> list[int]:
    base: list[int] = []
    for digit, count in enumerate(freq):
        if count < 0:
            raise ValueError(f"negative frequency for digit {digit}: {count}")
        base.extend([digit] * count)
    return base


def count_digits(digits: list[int]) -> list[int]:
    freq = [0] * 10
    for digit in digits:
        freq[digit] += 1
    return freq


def compute_k_moments(freq: list[int]) -> tuple[int, int, int]:
    k1 = sum(E1[i] * freq[i] for i in range(10))
    k2 = sum(E2[i] * freq[i] for i in range(10))
    k3 = sum(E3[i] * freq[i] for i in range(10))
    return k1, k2, k3


def encode_frequency_coords(freq: list[int]) -> dict:
    k1, k2, k3 = compute_k_moments(freq)
    return {
        "N": sum(freq),
        "K": [k1, k2, k3],
        "A": list(freq[:6]),
    }


def decode_frequency_coords(coords: dict) -> list[int]:
    n = int(coords["N"])
    k1, k2, k3 = [int(v) for v in coords["K"]]
    anchors = [int(v) for v in coords["A"]]
    if len(anchors) != 6:
        raise ValueError("expected 6 anchor counts in coords['A']")

    rhs = [
        n - sum(anchors),
        k1 - sum(E1[i] * anchors[i] for i in range(6)),
        k2 - sum(E2[i] * anchors[i] for i in range(6)),
        k3 - sum(E3[i] * anchors[i] for i in range(6)),
    ]

    tail = []
    for row in TAIL_INV:
        tail.append(sum(row[j] * rhs[j] for j in range(4)))

    freq = anchors + tail
    if any(value < 0 for value in freq):
        raise ValueError(f"decoded negative frequency vector: {freq}")

    # Guard against malformed packets.
    if sum(freq) != n or list(compute_k_moments(freq)) != [k1, k2, k3]:
        raise ValueError("coordinate decode failed validation")

    return freq


def build_permutation(target: list[int], base: list[int]) -> list[int]:
    """
    Build permutation P where target[i] = base[P[i]].
    We keep the earlier fixed-point maximisation strategy for duplicate digits.
    """
    n = len(target)
    tgt_pos: dict[int, list[int]] = defaultdict(list)
    src_pos: dict[int, list[int]] = defaultdict(list)

    for i, value in enumerate(target):
        tgt_pos[value].append(i)
    for j, value in enumerate(base):
        src_pos[value].append(j)

    perm = [-1] * n
    for value in tgt_pos:
        t_indices = tgt_pos[value]
        s_indices = src_pos[value]

        fixed = sorted(set(t_indices) & set(s_indices))
        used_t = set()
        used_s = set()

        for pos in fixed:
            perm[pos] = pos
            used_t.add(pos)
            used_s.add(pos)

        t_rem = [p for p in t_indices if p not in used_t]
        s_rem = [p for p in s_indices if p not in used_s]
        for t_pos, s_pos in zip(t_rem, s_rem):
            perm[t_pos] = s_pos

    return perm


def decompose_cycles(perm: list[int]) -> list[list[int]]:
    visited = [False] * len(perm)
    cycles: list[list[int]] = []

    for start in range(len(perm)):
        if visited[start]:
            continue
        cycle: list[int] = []
        current = start
        while not visited[current]:
            visited[current] = True
            cycle.append(current)
            current = perm[current]
        cycles.append(cycle)

    return cycles


def minimum_transpositions(cycles: list[list[int]]) -> int:
    return sum(len(cycle) - 1 for cycle in cycles if len(cycle) > 1)


def canonical_cycle(cycle: list[int]) -> list[int]:
    if len(cycle) <= 1:
        return list(cycle)
    start = min(range(len(cycle)), key=lambda idx: cycle[idx])
    return cycle[start:] + cycle[:start]


def apply_cycles(base: list[int], cycles: list[list[int]]) -> list[int]:
    result = list(base)
    for cycle in cycles:
        if len(cycle) <= 1:
            continue
        values = [base[cycle[(i + 1) % len(cycle)]] for i in range(len(cycle))]
        for i, pos in enumerate(cycle):
            result[pos] = values[i]
    return result


def zigzag_encode(value: int) -> int:
    return (value << 1) ^ (value >> 63) if value < 0 else value << 1


def zigzag_decode(value: int) -> int:
    return (value >> 1) ^ -(value & 1)


def encode_uvarint(value: int) -> bytes:
    if value < 0:
        raise ValueError("uvarint cannot encode negative values")
    out = bytearray()
    while value >= 0x80:
        out.append((value & 0x7F) | 0x80)
        value >>= 7
    out.append(value)
    return bytes(out)


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


def encode_svarint(value: int) -> bytes:
    return encode_uvarint(zigzag_encode(value))


def decode_svarint(data: bytes, offset: int) -> tuple[int, int]:
    raw, offset = decode_uvarint(data, offset)
    return zigzag_decode(raw), offset


def encode_cycles_path(cycles: list[list[int]]) -> bytes:
    """
    Delta-varint encoding for non-trivial cycles.
    We rotate each cycle so its smallest position comes first, and sort cycles by
    that first position. This keeps the representation deterministic.
    """
    non_trivial = [canonical_cycle(cycle) for cycle in cycles if len(cycle) > 1]
    non_trivial.sort(key=lambda cycle: cycle[0])

    out = bytearray()
    out.extend(encode_uvarint(len(non_trivial)))

    prev_cycle_start = 0
    for cycle in non_trivial:
        out.extend(encode_uvarint(len(cycle)))
        out.extend(encode_uvarint(cycle[0] - prev_cycle_start))
        prev_cycle_start = cycle[0]

        prev = cycle[0]
        for pos in cycle[1:]:
            out.extend(encode_svarint(pos - prev))
            prev = pos

    return bytes(out)


def decode_cycles_path(data: bytes) -> list[list[int]]:
    offset = 0
    n_cycles, offset = decode_uvarint(data, offset)
    cycles: list[list[int]] = []
    prev_cycle_start = 0

    for _ in range(n_cycles):
        length, offset = decode_uvarint(data, offset)
        first_delta, offset = decode_uvarint(data, offset)
        first = prev_cycle_start + first_delta
        prev_cycle_start = first

        cycle = [first]
        prev = first
        for _ in range(length - 1):
            delta, offset = decode_svarint(data, offset)
            prev = prev + delta
            cycle.append(prev)
        cycles.append(cycle)

    if offset != len(data):
        raise ValueError("trailing bytes in PATH payload")
    return cycles


def coords_payload_bytes(coords: dict) -> int:
    size = 0
    size += len(encode_uvarint(int(coords["N"])))
    for value in coords["K"]:
        size += len(encode_svarint(int(value)))
    for value in coords["A"]:
        size += len(encode_uvarint(int(value)))
    return size


def encode(data: bytes, verbose: bool = True) -> dict:
    t0 = time.time()

    digits = bytes_to_digits(data)
    freq = count_digits(digits)
    coords = encode_frequency_coords(freq)
    base = build_base_sequence(freq)

    perm = build_permutation(digits, base)
    cycles = decompose_cycles(perm)
    distance = minimum_transpositions(cycles)
    path = encode_cycles_path(cycles)
    digest = hashlib.sha256("".join(str(d) for d in digits).encode()).hexdigest()

    packet = {
        "V": 5,
        "COORDS": coords,
        "D": distance,
        "PATH": path,
        "H": digest,
    }

    elapsed = time.time() - t0
    if verbose:
        coord_bytes = coords_payload_bytes(coords)
        total_bytes = 1 + coord_bytes + len(path) + 32
        non_trivial = sum(1 for cycle in cycles if len(cycle) > 1)
        print(f"  ENCODE: {len(data):,} bytes = {len(digits):,} digits")
        print(f"    Coords: {coord_bytes} bytes")
        print(f"    Path: {len(path):,} bytes")
        print(f"    Distance: {distance:,} transpositions")
        print(f"    Non-trivial cycles: {non_trivial:,}")
        print(f"    Packet: ~{total_bytes:,} bytes")
        print(f"    Time: {elapsed:.3f}s")

    return packet


def decode(packet: dict, verbose: bool = True) -> bytes | None:
    t0 = time.time()

    freq = decode_frequency_coords(packet["COORDS"])
    base = build_base_sequence(freq)
    cycles = decode_cycles_path(packet["PATH"])
    digits = apply_cycles(base, cycles)

    digest = hashlib.sha256("".join(str(d) for d in digits).encode()).hexdigest()
    ok = digest == packet["H"]
    elapsed = time.time() - t0

    if verbose:
        print(f"  DECODE: {len(digits):,} digits")
        print(f"    Hash: {'OK' if ok else 'MISMATCH'}")
        print(f"    Time: {elapsed:.3f}s")

    if not ok:
        return None
    return digits_to_bytes(digits)


def compare_with_v2_style(packet: dict, digits: list[int]) -> tuple[int, int]:
    """
    Compare the exact-coordinate payload against the earlier v2 fallback model:
      1 + 12 + 20 + fixed-width cycle bytes + 32
    The v2 figure is only an estimate here, but it gives a clean baseline.
    """
    n = len(digits)
    cycles = decode_cycles_path(packet["PATH"])
    non_trivial = [cycle for cycle in cycles if len(cycle) > 1]
    width = 1 if n < 256 else 2 if n < 65536 else 3
    fixed_cycle_bytes = 1 + 2 + sum(2 + len(cycle) * width for cycle in non_trivial)
    old_packet = 1 + 12 + 20 + fixed_cycle_bytes + 32
    new_packet = 1 + coords_payload_bytes(packet["COORDS"]) + len(packet["PATH"]) + 32
    return old_packet, new_packet


def run_case(name: str, data: bytes) -> bool:
    print(f"\n{'=' * 72}")
    print(f"  {name}")
    print(f"  Input: {len(data):,} bytes")
    print(f"{'=' * 72}")

    packet = encode(data, verbose=True)
    result = decode(packet, verbose=True)
    ok = result == data

    digits = bytes_to_digits(data)
    old_packet, new_packet = compare_with_v2_style(packet, digits)
    print(f"  Packet comparison: v2-style ~{old_packet:,} bytes vs v5 ~{new_packet:,} bytes")
    print(f"  Verify: {'BIT-PERFECT' if ok else 'FAILED'}")
    return ok


def run_frequency_self_test() -> None:
    test_vectors = [
        [3, 7, 1, 9, 5, 4, 2, 6, 8, 10],
        [300, 298, 305, 299, 301, 297, 302, 304, 296, 298],
        [0, 0, 0, 0, 0, 0, 10, 20, 30, 40],
    ]
    for freq in test_vectors:
        coords = encode_frequency_coords(freq)
        rebuilt = decode_frequency_coords(coords)
        if rebuilt != freq:
            raise AssertionError((freq, coords, rebuilt))


if __name__ == "__main__":
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V5 - EXACT COORDS + DETERMINISTIC PATH                ║")
    print("║  Coordinate-only content reconstruction, no FREQ fallback   ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    run_frequency_self_test()

    total = 0
    passed = 0

    cases: list[tuple[str, bytes]] = [
        ("Hello payload", b"Hello KPOG recipe path"),
        ("Sequential bytes", bytes(range(64))),
        ("Repeated pattern", bytes([10, 20, 30, 40, 50] * 40)),
        ("Random 256B", os.urandom(256)),
        ("Random 1KB", os.urandom(1024)),
    ]

    real_file = "/Users/trentpalelei/Downloads/d345a5ca-975d-4a25-a4ca-59cf532e0792.jpeg"
    if os.path.exists(real_file):
        with open(real_file, "rb") as handle:
            cases.append(("Real JPEG slice 2KB", handle.read(2048)))

    for name, data in cases:
        total += 1
        if run_case(name, data):
            passed += 1

    print(f"\n{'=' * 72}")
    print(f"  SUMMARY: {passed}/{total} cases passed")
    print(f"{'=' * 72}")

