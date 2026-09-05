#!/usr/bin/env python3
"""
RIDE V10 - Whole-file TSP-guided address family.

This is the first whole-file family built around the user's framing:

  packet = { COORDS, FAM, ADDR, H }

Where:
  - COORDS rebuild the full unordered content
  - FAM selects a decoder-known canonical whole-file family
  - ADDR is the address inside that family
  - H verifies bit-perfect reconstruction

The new family in this prototype is:

  FAMILY_WHOLE_LANES
    1. Rebuild a deterministic K-base from coords using a balanced
       low-discrepancy interleaver, not a naive sorted run.
    2. Split the whole stream into interleaved lanes with stride S.
    3. Unrank each lane independently. The decoder already knows the rule.

This is still exact materialisation, but now the family is genuinely global
across the whole file rather than block slicing.

The TSP/thermo engine contributes:
  - exact mile = minimum transpositions from K-base to target
  - displacement spans that suggest candidate lane strides
"""

from __future__ import annotations

import argparse
import hashlib
import heapq
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

from ride_v6_kcoords_addr import (
    bytes_to_digits,
    count_digits,
    coords_payload_bytes,
    decode_frequency_coords,
    digits_to_bytes,
    encode_frequency_coords,
    encode_uvarint,
    rank_permutation_fast,
    unrank_permutation_fast,
)


FAMILY_WHOLE_LANES = 3
FAMILY_FULL_RANK = 255


def digit_hash(digits: list[int] | bytearray) -> str:
    return hashlib.sha256("".join(str(d) for d in digits).encode()).hexdigest()


def build_balanced_k_base(freq: list[int]) -> bytearray:
    """
    Deterministic whole-stream K-base.

    Each digit occurrence is placed on a low-discrepancy schedule so the base
    contains the right digits but is globally interleaved rather than sorted
    into ten solid runs.
    """
    total = sum(freq)
    if total == 0:
        return bytearray()

    heap: list[tuple[float, int, int, float, int]] = []
    for digit, count in enumerate(freq):
        if count <= 0:
            continue
        step = total / count
        first = step / 2.0
        heapq.heappush(heap, (first, digit, 1, step, count))

    out = bytearray()
    while heap:
        position, digit, emitted, step, count = heapq.heappop(heap)
        out.append(digit)
        if emitted < count:
            heapq.heappush(heap, (position + step, digit, emitted + 1, step, count))
    return out


def build_sorted_base(freq: list[int]) -> bytearray:
    out = bytearray()
    for digit, count in enumerate(freq):
        out.extend([digit] * count)
    return out


def exact_cycle_stats(target_digits: list[int] | bytearray, base_digits: list[int] | bytearray) -> dict:
    """
    Exact cycle/mile statistics for the fixed-point-maximising same-digit matching.

    This is the lightweight whole-file version of the thermo engine:
      mile = N - number_of_cycles
    """
    n = len(target_digits)
    target_pos = [array("I") for _ in range(10)]
    base_pos = [array("I") for _ in range(10)]

    for index, digit in enumerate(target_digits):
        target_pos[digit].append(index)
    for index, digit in enumerate(base_digits):
        base_pos[digit].append(index)

    perm = array("I", [0]) * n
    fixed_points = 0

    for digit in range(10):
        tgt = target_pos[digit]
        src = base_pos[digit]
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
                fixed_points += 1
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

    visited = bytearray(n)
    cycles = 0
    total_span = 0
    max_span = 0

    for index in range(n):
        span = abs(index - perm[index])
        total_span += span
        if span > max_span:
            max_span = span

        if visited[index]:
            continue
        cycles += 1
        current = index
        while not visited[current]:
            visited[current] = 1
            current = perm[current]

    return {
        "n": n,
        "mile": n - cycles,
        "cycles": cycles,
        "fixed_points": fixed_points,
        "mean_span": total_span / n if n else 0.0,
        "max_span": max_span,
    }


def next_power_two(value: int) -> int:
    if value <= 1:
        return 2
    return 1 << (value - 1).bit_length()


def candidate_lane_strides(stats: dict) -> list[int]:
    n = int(stats["n"])
    mean_span = max(2, int(stats["mean_span"]))
    max_span = max(2, int(stats["max_span"]))

    raw = {
        2,
        4,
        8,
        16,
        32,
        64,
        128,
        256,
        512,
        1024,
        2048,
        4096,
        next_power_two(mean_span),
        next_power_two(max_span),
        next_power_two(max(2, mean_span // 2)),
        next_power_two(max(2, max_span // 2)),
        next_power_two(max(2, int(math.sqrt(mean_span)))),
        next_power_two(max(2, int(math.sqrt(max_span)))),
    }

    upper = min(n, 16384)
    return sorted(value for value in raw if 2 <= value <= upper)


def lane_digit_counts(seq: list[int] | bytearray, stride: int) -> list[list[int]]:
    counts = [[0] * 10 for _ in range(stride)]
    lane = 0
    for digit in seq:
        counts[lane][digit] += 1
        lane += 1
        if lane == stride:
            lane = 0
    return counts


def split_lanes(seq: list[int] | bytearray, stride: int) -> list[list[int]]:
    lanes: list[list[int]] = [[] for _ in range(stride)]
    lane = 0
    for digit in seq:
        lanes[lane].append(int(digit))
        lane += 1
        if lane == stride:
            lane = 0
    return lanes


def merge_lanes(lanes: list[list[int]], total: int) -> list[int]:
    positions = [0] * len(lanes)
    out = [0] * total
    lane = 0
    for index in range(total):
        out[index] = lanes[lane][positions[lane]]
        positions[lane] += 1
        lane += 1
        if lane == len(lanes):
            lane = 0
    return out


def pack_lane_address(stride: int, mile: int, ranks: list[int]) -> bytes:
    out = bytearray()
    out.extend(encode_uvarint(stride))
    out.extend(encode_uvarint(mile))
    out.extend(encode_uvarint(len(ranks)))
    for rank in ranks:
        out.extend(encode_uvarint(rank))
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


def unpack_lane_address(data: bytes) -> tuple[int, int, list[int]]:
    offset = 0
    stride, offset = decode_uvarint(data, offset)
    mile, offset = decode_uvarint(data, offset)
    count, offset = decode_uvarint(data, offset)
    ranks: list[int] = []
    for _ in range(count):
        rank, offset = decode_uvarint(data, offset)
        ranks.append(rank)
    if offset != len(data):
        raise ValueError("trailing bytes in lane address")
    return stride, mile, ranks


def decode_whole_lanes_digits(freq: list[int], address: bytes) -> list[int]:
    stride, _mile, ranks = unpack_lane_address(address)
    base = build_balanced_k_base(freq)
    base_lanes = split_lanes(base, stride)
    if len(base_lanes) != len(ranks):
        raise ValueError("lane address count mismatch")

    out_lanes: list[list[int]] = []
    for base_lane, rank in zip(base_lanes, ranks):
        lane_freq = count_digits(base_lane)
        out_lanes.append(unrank_permutation_fast(rank, lane_freq, len(base_lane)))
    return merge_lanes(out_lanes, len(base))


def try_whole_lane_family(target_digits: list[int] | bytearray, verbose: bool = True) -> tuple[dict, dict] | None:
    freq = count_digits(target_digits)
    base = build_balanced_k_base(freq)
    stats = exact_cycle_stats(target_digits, base)
    candidates = candidate_lane_strides(stats)
    coords = encode_frequency_coords(freq)
    best_packet: dict | None = None
    best_meta: dict | None = None
    best_size: int | None = None

    if verbose:
        print(
            "  TSP stats: "
            f"mile={stats['mile']:,} cycles={stats['cycles']:,} "
            f"fixed={stats['fixed_points']:,} mean_span={stats['mean_span']:.1f} "
            f"max_span={stats['max_span']:,}"
        )
        print(f"  Candidate strides: {candidates}")

    for stride in candidates:
        t0 = time.perf_counter()
        base_lane_counts = lane_digit_counts(base, stride)
        target_lane_counts = lane_digit_counts(target_digits, stride)
        if base_lane_counts != target_lane_counts:
            if verbose:
                elapsed = time.perf_counter() - t0
                print(f"    whole_lanes[{stride}]: no exact hit ({elapsed:.2f}s)")
            continue

        base_lanes = split_lanes(base, stride)
        target_lanes = split_lanes(target_digits, stride)
        ranks = [
            rank_permutation_fast(target_lane, count_digits(target_lane))
            for target_lane in target_lanes
        ]
        address = pack_lane_address(stride, stats["mile"], ranks)
        packet = {
            "V": 10,
            "COORDS": coords,
            "FAM": FAMILY_WHOLE_LANES,
            "ADDR": address,
            "H": digit_hash(target_digits),
        }
        decoded = decode_whole_lanes_digits(freq, address)
        if decoded != list(target_digits):
            if verbose:
                print(f"    whole_lanes[{stride}]: decode mismatch, rejecting")
            continue

        size = packet_bytes(packet)
        meta = {
            "family": "whole_lanes",
            "stride": stride,
            "mile": stats["mile"],
            "address_bytes": len(address),
            "coord_bytes": coords_payload_bytes(coords),
            "encode_time_s": time.perf_counter() - t0,
        }
        if verbose:
            print(
                f"    whole_lanes[{stride}]: HIT "
                f"addr={len(address):,}B packet={size:,}B "
                f"time={meta['encode_time_s']:.2f}s"
            )

        if best_size is None or size < best_size:
            best_packet = packet
            best_meta = meta
            best_size = size

    if best_packet is None or best_meta is None:
        return None
    return best_packet, best_meta


def full_rank_packet(target_digits: list[int] | bytearray) -> tuple[dict, dict]:
    freq = count_digits(target_digits)
    coords = encode_frequency_coords(freq)
    address = rank_permutation_fast(list(target_digits), freq)
    packet = {
        "V": 10,
        "COORDS": coords,
        "FAM": FAMILY_FULL_RANK,
        "ADDR": address,
        "H": digit_hash(target_digits),
    }
    meta = {
        "family": "full_rank",
        "address_bytes": max(1, (int(address).bit_length() + 7) // 8),
        "coord_bytes": coords_payload_bytes(coords),
    }
    return packet, meta


def encode_digits(target_digits: list[int] | bytearray, allow_fallback: bool = True, verbose: bool = True) -> dict:
    t0 = time.perf_counter()
    result = try_whole_lane_family(target_digits, verbose=verbose)
    if result is not None:
        packet, meta = result
        if verbose:
            print(
                f"  Selected family={meta['family']} stride={meta['stride']} "
                f"mile={meta['mile']:,} packet={packet_bytes(packet):,}B"
            )
            print(f"  Encode total: {time.perf_counter() - t0:.2f}s")
        return packet

    if not allow_fallback:
        raise ValueError("no exact whole-file family hit under current dictionary")

    packet, meta = full_rank_packet(target_digits)
    if verbose:
        print(f"  Selected fallback family={meta['family']} packet={packet_bytes(packet):,}B")
        print(f"  Encode total: {time.perf_counter() - t0:.2f}s")
    return packet


def decode_digits(packet: dict, verbose: bool = True) -> list[int] | None:
    t0 = time.perf_counter()
    freq = decode_frequency_coords(packet["COORDS"])
    family = int(packet["FAM"])

    if family == FAMILY_WHOLE_LANES:
        digits = decode_whole_lanes_digits(freq, packet["ADDR"])
        family_name = "whole_lanes"
    elif family == FAMILY_FULL_RANK:
        digits = unrank_permutation_fast(int(packet["ADDR"]), freq, sum(freq))
        family_name = "full_rank"
    else:
        raise ValueError(f"unknown family id: {family}")

    ok = digit_hash(digits) == packet["H"]
    if verbose:
        print(
            f"  DECODE: family={family_name} "
            f"hash={'OK' if ok else 'MISMATCH'} "
            f"time={time.perf_counter() - t0:.2f}s"
        )
    return digits if ok else None


def encode_bytes(data: bytes, allow_fallback: bool = True, verbose: bool = True) -> dict:
    return encode_digits(bytes_to_digits(data), allow_fallback=allow_fallback, verbose=verbose)


def decode_bytes(packet: dict, verbose: bool = True) -> bytes | None:
    digits = decode_digits(packet, verbose=verbose)
    if digits is None:
        return None
    return digits_to_bytes(digits)


def packet_bytes(packet: dict) -> int:
    coord_bytes = coords_payload_bytes(packet["COORDS"])
    address = packet["ADDR"]
    if isinstance(address, bytes):
        address_bytes = len(address)
    else:
        address_bytes = max(1, (int(address).bit_length() + 7) // 8)
    return 1 + coord_bytes + 1 + address_bytes + 32


def make_lane_family_digits(freq: list[int], stride: int) -> list[int]:
    base = build_balanced_k_base(freq)
    base_lanes = split_lanes(base, stride)
    out_lanes: list[list[int]] = []
    for lane_index, lane in enumerate(base_lanes):
        rotated = list(lane)
        if rotated:
            shift = (lane_index * 7 + len(lane) // 5) % len(rotated)
            rotated = rotated[shift:] + rotated[:shift]
        out_lanes.append(rotated)
    return merge_lanes(out_lanes, len(base))


def run_digit_case(name: str, digits: list[int], allow_fallback: bool = False) -> bool:
    print(f"\n{'=' * 72}")
    print(f"  {name}")
    print(f"  Input: {len(digits):,} digits")
    print(f"{'=' * 72}")

    try:
        packet = encode_digits(digits, allow_fallback=allow_fallback, verbose=True)
    except ValueError as exc:
        print(f"  ENCODE FAILED: {exc}")
        return False

    result = decode_digits(packet, verbose=True)
    ok = result == digits
    print(f"  Packet bytes: ~{packet_bytes(packet):,}")
    print(f"  Verify: {'BIT-PERFECT' if ok else 'FAILED'}")
    return ok


def run_file_probe(path: Path) -> bool:
    data = path.read_bytes()
    digits = bytes_to_digits(data)
    freq = count_digits(digits)
    sorted_stats = exact_cycle_stats(digits, build_sorted_base(freq))
    balanced_stats = exact_cycle_stats(digits, build_balanced_k_base(freq))

    print(f"\n{'=' * 72}")
    print(f"  Whole-file probe: {path.name}")
    print(f"  Input: {len(data):,} bytes = {len(digits):,} digits")
    print(f"{'=' * 72}")
    print(
        "  Mile comparison: "
        f"sorted={sorted_stats['mile']:,} "
        f"balanced={balanced_stats['mile']:,}"
    )
    print(
        "  Mean span comparison: "
        f"sorted={sorted_stats['mean_span']:.1f} "
        f"balanced={balanced_stats['mean_span']:.1f}"
    )

    try:
        packet = encode_digits(digits, allow_fallback=False, verbose=True)
    except ValueError as exc:
        print(f"  WHOLE-FILE FAMILY MISS: {exc}")
        return False

    decoded = decode_bytes(packet, verbose=True)
    ok = decoded == data
    print(f"  Packet bytes: ~{packet_bytes(packet):,}")
    print(f"  Ratio: {len(data) / packet_bytes(packet):.2f}x")
    print(f"  Verify: {'BIT-PERFECT' if ok else 'FAILED'}")
    return ok


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Whole-file TSP-guided family probe.")
    parser.add_argument(
        "--file",
        help="Whole file to probe without fallback",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V10 - WHOLE-FILE TSP ADDRESS FAMILY                   ║")
    print("║  Balanced K-base + exact mile + global lane family          ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    total = 0
    passed = 0

    synthetic_cases = [
        ("Lane family exact hit (6,400 digits)", make_lane_family_digits([640] * 10, 64)),
        ("Lane family exact hit (30,000 digits)", make_lane_family_digits([3000] * 10, 128)),
    ]

    for name, digits in synthetic_cases:
        total += 1
        if run_digit_case(name, digits, allow_fallback=False):
            passed += 1

    if args.file:
        total += 1
        if run_file_probe(Path(args.file).expanduser()):
            passed += 1

    print(f"\n{'=' * 72}")
    print(f"  SUMMARY: {passed}/{total} passed")
    print(f"{'=' * 72}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
