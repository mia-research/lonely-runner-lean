#!/usr/bin/env python3
"""
Check the borrow-normal-form inner-asymmetry lemma on the local canonical
base-10 fixed-point corpus.

For a gap profile g with positive tail beta = g_m and outer gap alpha = g_1,
the lemma predicts the inner asymmetry vector

    (c1-c8, c2-c7, c3-c6, c4-c5)

depends only on (alpha, beta).
"""

from __future__ import annotations

import csv
import json
from collections import Counter, defaultdict
from pathlib import Path


DATA_FILES = [
    Path("/Users/trentpalelei/Desktop/Kaprekar/data/base10/canonical/kaprekar_d3-100_verified.csv"),
    Path("/Users/trentpalelei/Desktop/Kaprekar/data/base10/canonical/kaprekar_d101-150.csv"),
]

OUT = Path("/Users/trentpalelei/Desktop/Kaprekar/analysis/base10/inner_asymmetry_check_2026-04-23.json")
TMP_OUT = Path("/tmp/inner_asymmetry_check_2026-04-23.json")


def counts_from_n(n: str) -> tuple[int, ...]:
    c = [0] * 10
    for ch in n:
        c[ord(ch) - 48] += 1
    return tuple(c)


def gap_profile_from_n(n: str) -> tuple[int, ...]:
    ds = sorted((ord(ch) - 48 for ch in n), reverse=True)
    h = len(ds) // 2
    return tuple(ds[i] - ds[-1 - i] for i in range(h))


def positive_tail(g: tuple[int, ...]) -> tuple[int, int]:
    m = len(g)
    while m > 0 and g[m - 1] == 0:
        m -= 1
    if m == 0:
        raise ValueError(f"trivial all-zero gap profile: {g}")
    return g[0], g[m - 1]


def actual_asymmetry(c: tuple[int, ...]) -> tuple[int, int, int, int]:
    return (c[1] - c[8], c[2] - c[7], c[3] - c[6], c[4] - c[5])


def predicted_delta(alpha: int, beta: int, x: int) -> int:
    return (
        (1 if alpha == x else 0)
        - (1 if alpha == x + 1 else 0)
        - (1 if alpha == 9 - x else 0)
        + (1 if alpha == 10 - x else 0)
        - (1 if beta == x else 0)
        + (1 if beta == x + 1 else 0)
        + (1 if beta == 9 - x else 0)
        - (1 if beta == 10 - x else 0)
    )


def predicted_asymmetry(alpha: int, beta: int) -> tuple[int, int, int, int]:
    return tuple(predicted_delta(alpha, beta, x) for x in range(1, 5))


def main() -> None:
    checked = 0
    mismatches = []
    pair_counts = Counter()
    pair_examples: dict[tuple[int, int], str] = {}
    pair_asym = defaultdict(Counter)

    for path in DATA_FILES:
        with path.open() as fh:
            for row in csv.DictReader(fh):
                n = row.get("n")
                if not n:
                    continue
                g = gap_profile_from_n(n)
                alpha, beta = positive_tail(g)
                c = counts_from_n(n)
                actual = actual_asymmetry(c)
                predicted = predicted_asymmetry(alpha, beta)
                checked += 1
                pair_counts[(alpha, beta)] += 1
                pair_examples.setdefault((alpha, beta), n)
                pair_asym[(alpha, beta)][actual] += 1
                if actual != predicted and len(mismatches) < 50:
                    mismatches.append(
                        {
                            "d": len(n),
                            "n": n,
                            "gap_profile": list(g),
                            "pair": [alpha, beta],
                            "actual_asymmetry": list(actual),
                            "predicted_asymmetry": list(predicted),
                        }
                    )

    payload = {
        "checked_rows": checked,
        "pair_counts": {
            f"{a},{b}": pair_counts[(a, b)] for (a, b) in sorted(pair_counts)
        },
        "pair_examples": {
            f"{a},{b}": pair_examples[(a, b)] for (a, b) in sorted(pair_examples)
        },
        "pair_asymmetry_signatures": {
            f"{a},{b}": {str(k): v for k, v in pair_asym[(a, b)].items()}
            for (a, b) in sorted(pair_asym)
        },
        "mismatch_count": len(mismatches),
        "sample_mismatches": mismatches,
    }
    blob = json.dumps(payload, indent=2)
    try:
        OUT.write_text(blob)
        out = OUT
    except PermissionError:
        TMP_OUT.write_text(blob)
        out = TMP_OUT
    print(json.dumps({"json": str(out), **payload}, indent=2))


if __name__ == "__main__":
    main()
