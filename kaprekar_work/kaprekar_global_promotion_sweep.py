#!/usr/bin/env python3
"""
Global support sweep for the two remaining endgame claims:

1. Every fixed point has lead/tail pair in {(5,5),(6,2),(8,2),(9,1)}.
2. Every (9,1) fixed point satisfies the shell inequalities and fits E.
"""

from __future__ import annotations

import csv
import json
from collections import Counter
from pathlib import Path


DATA_FILES = [
    Path("/Users/trentpalelei/Desktop/Kaprekar/data/base10/canonical/kaprekar_d3-100_verified.csv"),
    Path("/Users/trentpalelei/Desktop/Kaprekar/data/base10/canonical/kaprekar_d101-150.csv"),
    Path("/Users/trentpalelei/Desktop/Kaprekar/data/base10/canonical/kaprekar_d101-1000_multiset.csv"),
]

OUT = Path("/Users/trentpalelei/Desktop/Kaprekar/analysis/base10/global_promotion_sweep_2026-04-23.json")
TMP_OUT = Path("/tmp/global_promotion_sweep_2026-04-23.json")

ALLOWED_PAIRS = {(5, 5), (6, 2), (8, 2), (9, 1)}


def counts_from_row(row: dict[str, str]) -> tuple[int, ...]:
    if "n" in row and row["n"]:
        c = [0] * 10
        for ch in row["n"]:
            c[ord(ch) - 48] += 1
        return tuple(c)
    return tuple(int(row[f"c{i}"]) for i in range(10))


def lead_tail_pair(c: tuple[int, ...]) -> tuple[int, int]:
    left = list(c)
    right = list(c)
    hi = 9
    lo = 0
    alpha = None
    beta = None

    while hi > lo:
        while hi > lo and left[hi] == 0:
            hi -= 1
        while lo < hi and right[lo] == 0:
            lo += 1
        if hi <= lo:
            break
        take = min(left[hi], right[lo])
        diff = hi - lo
        if diff > 0:
            if alpha is None:
                alpha = diff
            beta = diff
        left[hi] -= take
        right[lo] -= take

    if alpha is None or beta is None:
        raise ValueError(f"no positive shell pair for counts {c}")
    return alpha, beta


def e_branch_checks(c: tuple[int, ...]) -> dict[str, object]:
    z = c[0]
    q = c[9] - c[0]
    A, B, C, D = c[1], c[2], c[3], c[4]
    inequalities_ok = A >= q and B >= q and C >= q and D > q
    e_fit = (
        z >= 1
        and q >= 0
        and c[1] == c[2] == c[4] == c[5] == c[7] == c[8]
        and c[3] == c[6]
        and c[9] == z + q
        and c[1] - q >= 1
        and c[3] - q >= 0
    )
    return {
        "z": z,
        "q": q,
        "A": A,
        "B": B,
        "C": C,
        "D": D,
        "inequalities_ok": inequalities_ok,
        "e_fit": e_fit,
    }


def main() -> None:
    rows_scanned = 0
    pair_counts = Counter()
    bad_pairs = []
    e_rows = 0
    inequality_failures = []
    e_fit_failures = []

    for path in DATA_FILES:
        with path.open() as fh:
            for row in csv.DictReader(fh):
                d = int(row["d"])
                if path.name == "kaprekar_d101-1000_multiset.csv" and d <= 150:
                    continue
                c = counts_from_row(row)
                rows_scanned += 1
                pair = lead_tail_pair(c)
                pair_counts[pair] += 1
                if pair not in ALLOWED_PAIRS and len(bad_pairs) < 50:
                    bad_pairs.append({"d": d, "counts": list(c), "pair": list(pair)})
                if pair == (9, 1):
                    e_rows += 1
                    chk = e_branch_checks(c)
                    if not chk["inequalities_ok"] and len(inequality_failures) < 50:
                        inequality_failures.append({"d": d, "counts": list(c), **chk})
                    if not chk["e_fit"] and len(e_fit_failures) < 50:
                        e_fit_failures.append({"d": d, "counts": list(c), **chk})

    payload = {
        "rows_scanned": rows_scanned,
        "allowed_pairs": [list(x) for x in sorted(ALLOWED_PAIRS)],
        "pair_counts": {f"{a},{b}": pair_counts[(a, b)] for (a, b) in sorted(pair_counts)},
        "bad_pair_count": len(bad_pairs),
        "sample_bad_pairs": bad_pairs,
        "e_rows": e_rows,
        "e_inequality_failure_count": len(inequality_failures),
        "sample_e_inequality_failures": inequality_failures,
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
