#!/usr/bin/env python3
"""
RIDE V4 - Byte-space recipe prototype.

This removes the artificial decimal expansion from the earlier prototype.
We rank the permutation of the byte multiset directly:

  packet = { version, freq[256], rank, sha256 }

That is not the final KPOG packet, but it is a much fairer test of the
core recipe idea on realistic image data:
  - content comes from the multiset of bytes
  - order comes from the permutation rank
  - hash verifies bit-perfect reconstruction

Key optimisation:
  For remaining multiset size T with count vector f and permutation count M,
  the number of permutations beginning with any symbol in a prefix with
  cumulative count P is:

      M * P // T

  So ranking only needs the prefix count of smaller symbols, and unranking
  can choose the next symbol via order-statistics on the remaining counts.
"""

from __future__ import annotations

import hashlib
import math
import os
import time
from dataclasses import dataclass


ALPHABET = 256


class Fenwick:
    def __init__(self, size: int):
        self.size = size
        self.tree = [0] * (size + 1)

    @classmethod
    def from_counts(cls, counts: list[int]) -> "Fenwick":
        fw = cls(len(counts))
        for i, value in enumerate(counts):
            if value:
                fw.add(i, value)
        return fw

    def add(self, index: int, delta: int) -> None:
        i = index + 1
        while i <= self.size:
            self.tree[i] += delta
            i += i & -i

    def prefix_sum(self, index: int) -> int:
        total = 0
        i = index + 1
        while i > 0:
            total += self.tree[i]
            i -= i & -i
        return total

    def total(self) -> int:
        return self.prefix_sum(self.size - 1)

    def find_by_order(self, order: int) -> int:
        """Return smallest index i with prefix_sum(i) > order."""
        idx = 0
        bit = 1 << (self.size.bit_length() - 1)
        while bit:
            nxt = idx + bit
            if nxt <= self.size and self.tree[nxt] <= order:
                idx = nxt
                order -= self.tree[nxt]
            bit >>= 1
        return idx


def freq_from_bytes(data: bytes) -> list[int]:
    freq = [0] * ALPHABET
    for b in data:
        freq[b] += 1
    return freq


def multinomial(total: int, freq: list[int]) -> int:
    """Compute total! / prod(freq[i]!)."""
    result = 1
    remaining = total
    for count in freq:
        for k in range(1, count + 1):
            result = result * remaining // k
            remaining -= 1
    return result


def rank_permutation_bytes(data: bytes, freq: list[int]) -> int:
    counts = list(freq)
    tree = Fenwick.from_counts(counts)
    total = len(data)
    perms = multinomial(total, counts)
    rank = 0

    for symbol in data:
        smaller = tree.prefix_sum(symbol - 1) if symbol > 0 else 0
        if smaller:
            rank += perms * smaller // total

        count = counts[symbol]
        perms = perms * count // total
        counts[symbol] -= 1
        tree.add(symbol, -1)
        total -= 1
        if total == 0:
            break

    return rank


def unrank_permutation_bytes(rank: int, freq: list[int]) -> bytes:
    counts = list(freq)
    tree = Fenwick.from_counts(counts)
    total = sum(counts)
    perms = multinomial(total, counts)
    out = bytearray()

    while total:
        # q is the order statistic in the remaining sorted multiset.
        q = (rank * total) // perms
        symbol = tree.find_by_order(q)

        smaller = tree.prefix_sum(symbol - 1) if symbol > 0 else 0
        if smaller:
            rank -= perms * smaller // total

        out.append(symbol)
        count = counts[symbol]
        perms = perms * count // total
        counts[symbol] -= 1
        tree.add(symbol, -1)
        total -= 1

    return bytes(out)


def stirling_log2_factorial(n: int) -> float:
    if n <= 1:
        return 0.0
    return n * math.log2(n / math.e) + 0.5 * math.log2(2 * math.pi * n)


def predict_packet_size_bytes(data: bytes) -> dict[str, int | float]:
    freq = freq_from_bytes(data)
    total = len(data)
    log2_multi = stirling_log2_factorial(total)
    for count in freq:
        log2_multi -= stirling_log2_factorial(count)

    rank_bits = max(1, math.ceil(log2_multi))
    rank_bytes = (rank_bits + 7) // 8

    # Simple raw frequency payload for now: 256 counts as uint32 = 1024 bytes.
    # This is deliberately honest and easy to decode. We can compress it later.
    freq_bytes = 256 * 4
    hash_bytes = 32
    version_bytes = 1
    total_packet = version_bytes + freq_bytes + hash_bytes + rank_bytes

    return {
        "rank_bits": rank_bits,
        "rank_bytes": rank_bytes,
        "freq_bytes": freq_bytes,
        "hash_bytes": hash_bytes,
        "total_packet": total_packet,
        "ratio": len(data) / total_packet if total_packet else 0.0,
    }


@dataclass
class Packet:
    version: int
    freq: list[int]
    rank: int
    sha256: str


def encode_bytes(data: bytes, verbose: bool = True) -> Packet:
    t0 = time.time()
    freq = freq_from_bytes(data)
    rank = rank_permutation_bytes(data, freq)
    sha = hashlib.sha256(data).hexdigest()
    elapsed = time.time() - t0

    if verbose:
        rank_bits = max(1, rank.bit_length())
        rank_bytes = (rank_bits + 7) // 8
        packet_bytes = 1 + 32 + 256 * 4 + rank_bytes
        print(f"  ENCODE: {len(data):,} bytes")
        print(f"    Rank: {rank_bits:,} bits = {rank_bytes:,} bytes")
        print(f"    Packet: {packet_bytes:,} bytes")
        print(f"    Ratio: {len(data) / packet_bytes:.2f}x")
        print(f"    Time: {elapsed:.2f}s")

    return Packet(version=4, freq=freq, rank=rank, sha256=sha)


def decode_bytes(packet: Packet, verbose: bool = True) -> bytes | None:
    t0 = time.time()
    data = unrank_permutation_bytes(packet.rank, packet.freq)
    sha = hashlib.sha256(data).hexdigest()
    ok = sha == packet.sha256
    elapsed = time.time() - t0

    if verbose:
        print(f"  DECODE: {len(data):,} bytes")
        print(f"    Hash: {'OK' if ok else 'MISMATCH'}")
        print(f"    Time: {elapsed:.2f}s")

    return data if ok else None


def roundtrip_slice(filepath: str, max_bytes: int) -> bool:
    with open(filepath, "rb") as handle:
        data = handle.read(max_bytes)

    print(f"\n{'=' * 72}")
    print(f"  FILE: {os.path.basename(filepath)}  slice={len(data):,} bytes")
    print(f"{'=' * 72}")

    pred = predict_packet_size_bytes(data)
    print("  PREDICTION:")
    print(f"    Rank: {pred['rank_bytes']:,} bytes")
    print(f"    Packet: {pred['total_packet']:,} bytes")
    print(f"    Ratio: {pred['ratio']:.2f}x")

    packet = encode_bytes(data, verbose=True)
    decoded = decode_bytes(packet, verbose=True)
    ok = decoded == data
    print(f"  VERIFY: {'BIT-PERFECT' if ok else 'FAILED'}")
    return ok


def predict_file(filepath: str) -> dict[str, int | float]:
    with open(filepath, "rb") as handle:
        data = handle.read()
    pred = predict_packet_size_bytes(data)
    print(
        f"  {os.path.basename(filepath)[:30]:30s} | "
        f"{len(data):>10,}B | {pred['total_packet']:>10,}B | {pred['ratio']:>7.2f}x"
    )
    return pred


if __name__ == "__main__":
    files = [
        "/Users/trentpalelei/Downloads/d345a5ca-975d-4a25-a4ca-59cf532e0792.jpeg",
        "/Users/trentpalelei/Downloads/IMG_1545.jpeg",
        "/Users/trentpalelei/Downloads/Safety.jpg",
    ]

    print("RIDE V4 - BYTE-SPACE RECIPE TEST")
    print("\nSmall exact round-trips:")
    for size in (1024, 4096, 16384):
        roundtrip_slice(files[0], size)

    print(f"\n{'=' * 72}")
    print("Predicted full-file packet sizes")
    print(f"{'=' * 72}")
    print(f"  {'File':30s} | {'Raw':>10s} | {'Recipe':>10s} | {'Ratio':>7s}")
    print(f"  {'-' * 30}-+-{'-' * 10}-+-{'-' * 10}-+-{'-' * 7}")
    for filepath in files:
        predict_file(filepath)
