#!/usr/bin/env python3
"""
RIDE V11 - Actual K-constant probe.

This corrects the conceptual drift from v10:

  file -> one big decimal number
       -> choose an actual Kaprekar family member K of the same digit length
       -> if file digits are a permutation of K, encode as (family, k, rank)

This matches the local research statement:
  (family, k, permutation_rank)

The goal here is not yet a full arbitrary-file encoder. It is a clean probe that:
  1. uses lossless whole-file decimal conversion
  2. recreates the actual K constant, not a synthetic canonical base
  3. tests exact-permutation eligibility and frequency deltas on real files
"""

from __future__ import annotations

import argparse
import hashlib
import math
import random
import sys
import time
from collections import Counter
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(10_000_000)


def binary_to_decimal_lossless(data: bytes) -> str:
    if not data:
        return "0"
    return str(int.from_bytes(data, "big"))


def gen_495(k: int) -> str:
    if k < 1:
        raise ValueError("495 family requires k >= 1")
    if k == 1:
        return "495"
    return "5" * (k - 1) + "4" + "9" * k + "4" * (k - 1) + "5"


def gen_6174(k: int) -> str:
    if k < 0:
        raise ValueError("6174 family requires k >= 0")
    return "6" + "3" * k + "1" + "7" + "6" * k + "4"


def gen_864(k: int) -> str:
    if k < 0:
        raise ValueError("864 family requires k >= 0")
    return "864" + "3" * k + "197" + "6" * k + "532"


def candidate_k_constants(digits_len: int) -> list[tuple[str, int, str]]:
    out: list[tuple[str, int, str]] = []
    if digits_len >= 3 and digits_len % 3 == 0:
        k = digits_len // 3
        out.append(("495", k, gen_495(k)))
    if digits_len >= 4 and (digits_len - 4) % 2 == 0:
        k = (digits_len - 4) // 2
        out.append(("6174", k, gen_6174(k)))
    if digits_len >= 9 and (digits_len - 9) % 2 == 0:
        k = (digits_len - 9) // 2
        out.append(("864", k, gen_864(k)))
    return out


def count_permutations(multiset_counts: list[int]) -> int:
    total = sum(multiset_counts)
    result = math.factorial(total)
    for count in multiset_counts:
        result //= math.factorial(count)
    return result


def encode_permutation_small(s: str) -> int:
    digits = list(s)
    index = 0
    remaining = sorted(digits)

    for digit in digits:
        seen = set()
        rank = 0
        for candidate in remaining:
            if candidate >= digit or candidate in seen:
                continue
            seen.add(candidate)
            pool = remaining[:]
            pool.remove(candidate)
            counts = Counter(pool)
            rank += count_permutations(list(counts.values()))
        index += rank
        remaining.remove(digit)
    return index


def decode_permutation_small(sorted_chars: str, index: int) -> str:
    remaining = list(sorted_chars)
    result: list[str] = []
    length = len(sorted_chars)

    for _ in range(length):
        seen = set()
        for candidate in remaining:
            if candidate in seen:
                continue
            seen.add(candidate)
            pool = remaining[:]
            pool.remove(candidate)
            counts = Counter(pool)
            count = count_permutations(list(counts.values()))
            if index < count:
                result.append(candidate)
                remaining.remove(candidate)
                break
            index -= count
    return "".join(result)


def permutation_probe(target: str) -> list[dict]:
    target_counts = Counter(target)
    rows: list[dict] = []
    for family, k, k_str in candidate_k_constants(len(target)):
        k_counts = Counter(k_str)
        exact_perm = k_counts == target_counts
        delta = sum(abs(target_counts[str(d)] - k_counts[str(d)]) for d in range(10))
        rows.append(
            {
                "family": family,
                "k": k,
                "digits": len(target),
                "exact_permutation": exact_perm,
                "l1_freq_delta": delta,
                "k_hash": hashlib.sha256(k_str.encode()).hexdigest(),
            }
        )
    return rows


def run_small_roundtrip() -> bool:
    print(f"\n{'=' * 72}")
    print("  Small actual-K round-trip")
    print(f"{'=' * 72}")

    cases = [
        ("495", 8, gen_495(8)),
        ("6174", 10, gen_6174(10)),
    ]
    random.seed(42)
    passed = True

    for family, k, k_str in cases:
        digits = list(k_str)
        random.shuffle(digits)
        target = "".join(digits)
        index = encode_permutation_small(target)
        decoded = decode_permutation_small("".join(sorted(k_str)), index)
        ok = decoded == target
        bits = max(1, index.bit_length())
        print(
            f"  {family}-{k}: digits={len(k_str)} "
            f"index_bits={bits} verify={'OK' if ok else 'FAIL'}"
        )
        passed &= ok
    return passed


def run_file_probe(path: Path) -> bool:
    print(f"\n{'=' * 72}")
    print(f"  Whole-file actual-K probe: {path.name}")
    print(f"{'=' * 72}")

    data = path.read_bytes()
    t0 = time.perf_counter()
    decimal = binary_to_decimal_lossless(data)
    elapsed = time.perf_counter() - t0
    rows = permutation_probe(decimal)

    print(f"  Raw bytes: {len(data):,}")
    print(f"  Decimal digits: {len(decimal):,}")
    print(f"  Decimal conversion time: {elapsed:.2f}s")

    if not rows:
        print("  No supported K family for this digit length.")
        return False

    any_exact = False
    for row in rows:
        print(
            f"  {row['family']}-{row['k']}: "
            f"exact_perm={'YES' if row['exact_permutation'] else 'NO'} "
            f"l1_freq_delta={row['l1_freq_delta']:,}"
        )
        any_exact |= row["exact_permutation"]

    if any_exact:
        print("  At least one actual K family is an exact permutation source.")
    else:
        print("  No actual K family matched the file's full digit multiset exactly.")
    return any_exact


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Actual K-constant probe.")
    parser.add_argument("--file", help="Whole file to probe as one decimal number")
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V11 - ACTUAL K-CONSTANT PROBE                         ║")
    print("║  whole-file decimal -> real K family -> permutation test    ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    total = 0
    passed = 0

    total += 1
    if run_small_roundtrip():
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
