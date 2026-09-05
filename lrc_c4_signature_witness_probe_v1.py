from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from typing import Sequence

from lrc_c4_exact_active_core_certifier_v1 import (
    active_in_C4,
    bounded_global_cache,
    bounded_has_full_cover,
    bounded_witnesses,
    service_state_at_x,
)


def state_sig_for_subset(
    subset: Sequence[int],
    cells: Sequence[tuple[Fraction, Fraction]],
) -> tuple[tuple[tuple[int, ...], ...], ...]:
    active = tuple(v for v in subset if active_in_C4(Fraction(v, 1)))
    sig = []
    for left, right in cells:
        mid = (left + right) / 2
        states = tuple(service_state_at_x(Fraction(v, 1), mid) for v in active)
        sig.append(tuple(tuple(s) for s in states))
    return tuple(sig)


def witness_pairs(subset: Sequence[int]) -> set[tuple[int, int]]:
    return {(t.numerator, t.denominator) for t, _, _ in bounded_witnesses((1,) + tuple(subset), q_max=5)}


def analyze_bounded_signature_classes(max_speed: int = 17) -> dict[str, object]:
    cache = bounded_global_cache(max_speed)
    cells = cache["cells"]
    assert isinstance(cells, list)

    full_sig_classes: dict[
        tuple[tuple[tuple[int, ...], ...], ...],
        list[dict[str, object]],
    ] = defaultdict(list)

    for subset in combinations(range(2, max_speed + 1), 9):
        if not bounded_has_full_cover(subset, cache):
            continue
        sig = state_sig_for_subset(subset, cells)
        inactive = tuple(v for v in subset if not active_in_C4(Fraction(v, 1)))
        full_sig_classes[sig].append(
            {
                "subset": subset,
                "inactive": inactive,
                "witnesses": sorted(witness_pairs(subset)),
            }
        )

    multiplicity_hist = Counter(len(rows) for rows in full_sig_classes.values())
    signature_rows: list[dict[str, object]] = []
    bad_class_count = 0
    good_class_count = 0

    for sig, rows in full_sig_classes.items():
        intersections = [set(row["witnesses"]) for row in rows]
        common = sorted(set.intersection(*intersections))
        row = {
            "multiplicity": len(rows),
            "common_witnesses": common,
            "has_common_witness": bool(common),
            "subsets": [
                {
                    "subset": list(item["subset"]),
                    "inactive": list(item["inactive"]),
                    "witnesses": [list(pair) for pair in item["witnesses"]],
                }
                for item in rows
            ],
        }
        if common:
            good_class_count += 1
        else:
            bad_class_count += 1
        signature_rows.append(row)

    # A bounded refinement experiment: active signature + inactive set
    refined_classes: dict[tuple[object, tuple[int, ...]], list[set[tuple[int, int]]]] = defaultdict(list)
    for sig, rows in full_sig_classes.items():
        for row in rows:
            key = (sig, tuple(row["inactive"]))
            refined_classes[key].append(set(row["witnesses"]))

    refined_empty = sum(1 for rows in refined_classes.values() if not set.intersection(*rows))

    return {
        "max_speed": max_speed,
        "full_cover_count": sum(len(rows) for rows in full_sig_classes.values()),
        "distinct_full_signatures": len(full_sig_classes),
        "multiplicity_histogram": dict(sorted(multiplicity_hist.items())),
        "good_signature_classes": good_class_count,
        "bad_signature_classes": bad_class_count,
        "signature_rows": signature_rows,
        "inactive_refinement": {
            "class_count": len(refined_classes),
            "empty_common_witness_classes": refined_empty,
        },
    }


def print_summary(report: dict[str, object]) -> None:
    print("# C4 signature-level witness probe")
    print()
    print(f"- bounded window: v1=1, speeds in {{2,...,{report['max_speed']}}}")
    print(f"- full-cover subsets: {report['full_cover_count']}")
    print(f"- distinct ordered active signatures: {report['distinct_full_signatures']}")
    print(f"- multiplicity histogram: {report['multiplicity_histogram']}")
    print(f"- signature classes with common bounded witness: {report['good_signature_classes']}")
    print(f"- signature classes without common bounded witness: {report['bad_signature_classes']}")
    print(
        "- inactive refinement (signature + inactive set) leaves empty classes: "
        f"{report['inactive_refinement']['empty_common_witness_classes']}"
    )
    print()
    print("## Bad signature classes")
    bad_rows = [row for row in report["signature_rows"] if not row["has_common_witness"]]
    for idx, row in enumerate(bad_rows, 1):
        print(f"- class {idx}: multiplicity {row['multiplicity']}")
        for item in row["subsets"]:
            subset = item["subset"]
            inactive = item["inactive"]
            witnesses = item["witnesses"]
            print(
                "  subset="
                f"{subset}, inactive={inactive}, witnesses={witnesses}"
            )


def write_json(path: Path) -> None:
    report = analyze_bounded_signature_classes()
    with path.open("w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=2)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    report = analyze_bounded_signature_classes()
    if args.json_out is not None:
        with args.json_out.open("w", encoding="utf-8") as fh:
            json.dump(report, fh, indent=2)
    print_summary(report)
