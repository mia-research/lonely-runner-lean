#!/usr/bin/env python3
"""
Validate the shell-reduction formula on the local (9,1) branch.
"""

from __future__ import annotations

import csv
import json
from pathlib import Path


DATA_FILES = [
    Path("/Users/trentpalelei/Desktop/Kaprekar/data/base10/canonical/kaprekar_d3-100_verified.csv"),
    Path("/Users/trentpalelei/Desktop/Kaprekar/data/base10/canonical/kaprekar_d101-150.csv"),
]

OUT = Path("/Users/trentpalelei/Desktop/Kaprekar/analysis/base10/e_branch_shell_reduction_2026-04-23.json")
TMP_OUT = Path("/tmp/e_branch_shell_reduction_2026-04-23.json")


def counts(n: str) -> tuple[int, ...]:
    c = [0] * 10
    for ch in n:
        c[ord(ch) - 48] += 1
    return tuple(c)


def gap_profile(n: str) -> tuple[int, ...]:
    ds = sorted((ord(ch) - 48 for ch in n), reverse=True)
    h = len(ds) // 2
    return tuple(ds[i] - ds[-1 - i] for i in range(h))


def positive_tail_pair(g: tuple[int, ...]) -> tuple[int, int]:
    m = len(g)
    while m > 0 and g[m - 1] == 0:
        m -= 1
    return g[0], g[m - 1]


def predicted_gap_from_counts(c: tuple[int, ...]) -> tuple[int, ...]:
    z = c[0]
    q = c[9] - c[0]
    A, B, C, D = c[1], c[2], c[3], c[4]
    g = []
    g += [9] * z
    g += [8] * q
    g += [7] * (A - q)
    g += [6] * q
    g += [5] * (B - q)
    g += [4] * q
    g += [3] * (C - q)
    g += [2] * q
    g += [1] * (D - q)
    zeros = len(c)  # dummy, replaced by caller
    return tuple(g)


def main() -> None:
    checked = 0
    inequality_failures = []
    gap_failures = []
    e_fit_failures = []

    for path in DATA_FILES:
        with path.open() as fh:
            for row in csv.DictReader(fh):
                n = row.get("n")
                if not n:
                    continue
                g = gap_profile(n)
                if positive_tail_pair(g) != (9, 1):
                    continue

                c = counts(n)
                z = c[0]
                q = c[9] - c[0]
                A, B, C, D = c[1], c[2], c[3], c[4]
                checked += 1

                if not (A >= q and B >= q and C >= q and D > q):
                    if len(inequality_failures) < 20:
                        inequality_failures.append(
                            {
                                "n": n,
                                "counts": list(c),
                                "q": q,
                            }
                        )

                pred = list(predicted_gap_from_counts(c))
                pred += [0] * (len(g) - len(pred))
                if tuple(pred) != g and len(gap_failures) < 20:
                    gap_failures.append(
                        {
                            "n": n,
                            "actual_gap": list(g),
                            "predicted_gap": pred,
                            "counts": list(c),
                        }
                    )

                e_fit = (
                    c[1] == c[2] == c[4] == c[5] == c[7] == c[8]
                    and c[3] == c[6]
                    and c[9] >= c[0] >= 1
                )
                if not e_fit and len(e_fit_failures) < 20:
                    e_fit_failures.append(
                        {
                            "n": n,
                            "counts": list(c),
                        }
                    )

    payload = {
        "checked_rows": checked,
        "inequality_failure_count": len(inequality_failures),
        "sample_inequality_failures": inequality_failures,
        "gap_formula_failure_count": len(gap_failures),
        "sample_gap_formula_failures": gap_failures,
        "e_fit_failure_count": len(e_fit_failures),
        "sample_e_fit_failures": e_fit_failures,
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
