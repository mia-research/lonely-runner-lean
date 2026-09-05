#!/usr/bin/env python3
"""
RIDE V12 - Thermodynamic K-manifold probe.

This corrects the earlier family-only assumption by using:
  - the merged 106k Kaprekar database for validation
  - the constructive thermodynamic model from the decidability paper

Workflow:
  1. Treat a file as one lossless decimal number.
  2. Project its digit frequencies onto the thermodynamic manifold:
       counts[1,2,4,5,7,8] = a
       counts[3,6]         = b
       counts[0]           = v0
       counts[9]           = v9
  3. Construct the actual pivot-anchored seed.
  4. Iterate the Kaprekar map to materialise an actual K constant.
  5. Measure how close the file is to that actual constant.

This is still not the final encoder. It is the corrected K-source probe:
  actual K constant first, then delta/permutation after that.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import random
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(10_000_000)


DB_PATH = Path("/Users/trentpalelei/Downloads/kaprekar_d3_100_COMPLETE_MERGED.csv")
A_DIGITS = (1, 2, 4, 5, 7, 8)
B_DIGITS = (3, 6)


def binary_to_decimal_lossless(data: bytes) -> str:
    if not data:
        return "0"
    return str(int.from_bytes(data, "big"))


def digit_counts(s: str) -> list[int]:
    counts = [0] * 10
    for ch in s:
        counts[ord(ch) - 48] += 1
    return counts


def build_desc_from_counts(counts: list[int]) -> str:
    return "".join(str(digit) * counts[digit] for digit in range(9, -1, -1))


def subtract_decimal_strings(a: str, b: str) -> str:
    """
    Compute a - b for equal-length decimal strings, preserving leading zeros.
    Assumes a >= b.
    """
    borrow = 0
    out = ["0"] * len(a)
    for index in range(len(a) - 1, -1, -1):
        digit = (ord(a[index]) - 48) - (ord(b[index]) - 48) - borrow
        if digit < 0:
            digit += 10
            borrow = 1
        else:
            borrow = 0
        out[index] = chr(48 + digit)
    return "".join(out)


def kaprekar_step(s: str) -> str:
    counts = digit_counts(s)
    desc = build_desc_from_counts(counts)
    asc = desc[::-1]
    return subtract_decimal_strings(desc, asc)


def iterate_to_fixed(seed: str, max_iter: int = 30) -> tuple[str | None, int, str]:
    seen: dict[str, int] = {}
    current = seed
    for step in range(max_iter + 1):
        if current in seen:
            return None, step, "cycle"
        seen[current] = step
        nxt = kaprekar_step(current)
        if nxt == current:
            return current, step + 1, "fixed"
        current = nxt
    return None, max_iter, "timeout"


def infer_thermo_params_from_counts(counts: list[int]) -> tuple[int, int, int, int] | None:
    a_vals = [counts[d] for d in A_DIGITS]
    b_vals = [counts[d] for d in B_DIGITS]
    if len(set(a_vals)) != 1 or len(set(b_vals)) != 1:
        return None
    return counts[0], a_vals[0], b_vals[0], counts[9]


def thermo_counts_from_params(v0: int, a: int, b: int, v9: int) -> list[int]:
    counts = [0] * 10
    counts[0] = v0
    for digit in A_DIGITS:
        counts[digit] = a
    for digit in B_DIGITS:
        counts[digit] = b
    counts[9] = v9
    return counts


def construct_pivot_seed(counts: list[int]) -> str:
    remaining = list(counts)
    n = sum(remaining)

    if n % 2 == 1:
        if remaining[9] <= 0:
            raise ValueError("odd-length thermodynamic seed needs a central 9")
        remaining[9] -= 1
        tail = build_desc_from_counts(remaining)
        left = n // 2
        return tail[:left] + "9" + tail[left:]

    centers: list[str] = []
    for _ in range(2):
        if remaining[8] > 0:
            remaining[8] -= 1
            centers.append("8")
            continue
        # Fallback: use the largest available digit.
        for digit in range(9, -1, -1):
            if remaining[digit] > 0:
                remaining[digit] -= 1
                centers.append(str(digit))
                break
    tail = build_desc_from_counts(remaining)
    left = n // 2 - 2 // 2
    return tail[:left] + "".join(centers) + tail[left:]


def optimize_1d_with_anchor(values: list[int], anchor_scale: int, anchor_target: int) -> int:
    candidates = set(values)
    q, r = divmod(anchor_target, anchor_scale)
    candidates.update({q - 1, q, q + 1, q + 2})
    best_value = None
    best_cost = None
    for candidate in candidates:
        if candidate < 0:
            continue
        cost = sum(abs(value - candidate) for value in values)
        cost += abs(anchor_target - anchor_scale * candidate)
        if best_cost is None or cost < best_cost:
            best_cost = cost
            best_value = candidate
    assert best_value is not None
    return best_value


def nearest_thermo_params(target_counts: list[int]) -> tuple[int, int, int, int, int]:
    a_values = [target_counts[d] for d in A_DIGITS]
    b_values = [target_counts[d] for d in B_DIGITS]
    c0 = target_counts[0]
    c9 = target_counts[9]
    sum_ab = sum(a_values) + sum(b_values)

    a = sorted(a_values)[len(a_values) // 2]
    b = sorted(b_values)[len(b_values) // 2]

    # Convex block-coordinate descent to the exact integer optimum.
    for _ in range(16):
        new_a = optimize_1d_with_anchor(a_values, 6, sum_ab - 2 * b)
        new_b = optimize_1d_with_anchor(b_values, 2, sum_ab - 6 * new_a)
        if new_a == a and new_b == b:
            break
        a, b = new_a, new_b

    s = c0 + c9 + (sum_ab - (6 * a + 2 * b))
    v0_low = max(0, min(c0, s - c9))
    v0_high = min(s, max(c0, s - c9))
    v0 = v0_low
    v9 = s - v0

    thermo = thermo_counts_from_params(v0, a, b, v9)
    l1 = sum(abs(target_counts[d] - thermo[d]) for d in range(10))
    return v0, a, b, v9, l1


def load_db(path: Path) -> dict[int, set[str]]:
    db: dict[int, set[str]] = defaultdict(set)
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            constant = (row.get("constant") or row.get("kaprekar_constant") or "").strip()
            if not constant:
                continue
            dimension = int(row.get("dimension", row.get("d", 0)) or 0)
            db[dimension].add(constant)
    return db


def sample_thermo_rows(path: Path, per_dimension: int = 1, max_dimension: int = 40) -> list[dict]:
    by_dim: dict[int, list[dict]] = defaultdict(list)
    with path.open() as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            if row.get("type") != "thermodynamic":
                continue
            dimension = int(row.get("dimension", row.get("d", 0)) or 0)
            if dimension > max_dimension:
                continue
            by_dim[dimension].append(row)
    out: list[dict] = []
    random.seed(42)
    for dimension in sorted(by_dim):
        rows = by_dim[dimension]
        random.shuffle(rows)
        out.extend(rows[:per_dimension])
    return out


def validate_against_database(path: Path) -> bool:
    print(f"\n{'=' * 72}")
    print("  Validation against merged K database")
    print(f"{'=' * 72}")

    db = load_db(path)
    samples = sample_thermo_rows(path, per_dimension=1, max_dimension=40)
    passed = 0
    total = 0

    for row in samples[:12]:
        total += 1
        constant = row["constant"].strip()
        counts = digit_counts(constant)
        params = infer_thermo_params_from_counts(counts)
        if params is None:
            print(f"  d={len(constant)} skipped: not thermo-regular by counts")
            continue
        seed = construct_pivot_seed(counts)
        fixed, steps, status = iterate_to_fixed(seed, max_iter=30)
        ok = fixed is not None and fixed in db[len(constant)]
        if ok:
            passed += 1
        print(
            f"  d={len(constant):>3} steps={steps:>2} "
            f"status={status:<5} verify={'OK' if ok else 'FAIL'} "
            f"constant={constant[:36]}"
        )

    print(f"  Validation: {passed}/{total} exact database hits")
    return passed == total


def shared_multiset_size(a: list[int], b: list[int]) -> int:
    return sum(min(x, y) for x, y in zip(a, b))


def run_whole_file_probe(path: Path) -> None:
    print(f"\n{'=' * 72}")
    print(f"  Whole-file thermodynamic K probe: {path.name}")
    print(f"{'=' * 72}")

    raw = path.read_bytes()
    t0 = time.perf_counter()
    decimal = binary_to_decimal_lossless(raw)
    decimal_time = time.perf_counter() - t0

    target_counts = digit_counts(decimal)
    v0, a, b, v9, l1 = nearest_thermo_params(target_counts)
    thermo_counts = thermo_counts_from_params(v0, a, b, v9)

    print(f"  Raw bytes: {len(raw):,}")
    print(f"  Decimal digits: {len(decimal):,}")
    print(f"  Decimal conversion: {decimal_time:.2f}s")
    print(f"  Target counts: {target_counts}")
    print(f"  Nearest thermo params: v0={v0:,} a={a:,} b={b:,} v9={v9:,}")
    print(f"  L1 frequency delta: {l1:,}")
    print(f"  Shared multiset coverage: {shared_multiset_size(target_counts, thermo_counts):,} / {len(decimal):,}")

    t1 = time.perf_counter()
    seed = construct_pivot_seed(thermo_counts)
    fixed, steps, status = iterate_to_fixed(seed, max_iter=30)
    iter_time = time.perf_counter() - t1

    if fixed is None:
        print(f"  Kaprekar iteration status: {status} after {steps} steps")
        return

    fixed_counts = digit_counts(fixed)
    fixed_l1 = sum(abs(target_counts[d] - fixed_counts[d]) for d in range(10))
    print(f"  Materialised actual K constant in {steps} steps ({iter_time:.2f}s)")
    print(f"  Fixed prefix: {fixed[:80]}...")
    print(f"  Fixed hash: {hashlib.sha256(fixed.encode()).hexdigest()}")
    print(f"  Fixed-count L1 delta to file: {fixed_l1:,}")
    print(f"  Exact permutation source? {'YES' if fixed_counts == target_counts else 'NO'}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Thermodynamic K-manifold probe")
    parser.add_argument("--file", help="Whole file to probe as one lossless decimal number")
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V12 - THERMODYNAMIC K-MANIFOLD PROBE                  ║")
    print("║  database-backed actual-K source, then delta/permutation    ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    validate_against_database(DB_PATH)
    if args.file:
        run_whole_file_probe(Path(args.file).expanduser())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
