#!/usr/bin/env python3
"""Compare expected vs reproduced CSV/JSON artifacts."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any, Dict, Iterable, List, Tuple


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Independent reproduction comparator")
    p.add_argument("--expected", required=True)
    p.add_argument("--actual", required=True)
    p.add_argument("--output", required=True, help="Output JSON report")
    p.add_argument("--rtol", type=float, default=1e-7)
    p.add_argument("--atol", type=float, default=1e-10)
    return p.parse_args()


def flatten_json(obj: Any, prefix: str = "") -> List[Tuple[str, float]]:
    out: List[Tuple[str, float]] = []
    if isinstance(obj, dict):
        for k in sorted(obj.keys()):
            key = f"{prefix}.{k}" if prefix else str(k)
            out.extend(flatten_json(obj[k], key))
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            out.extend(flatten_json(v, f"{prefix}[{i}]"))
    elif isinstance(obj, (int, float)):
        out.append((prefix, float(obj)))
    return out


def csv_numeric_map(path: Path) -> Dict[str, float]:
    out: Dict[str, float] = {}
    with path.open(newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for ridx, row in enumerate(reader):
            for k, v in row.items():
                if v is None:
                    continue
                try:
                    out[f"row{ridx}.{k}"] = float(v)
                except ValueError:
                    continue
    return out


def load_numeric_map(path: Path) -> Dict[str, float]:
    suffix = path.suffix.lower()
    if suffix == ".json":
        data = json.loads(path.read_text(encoding="utf-8"))
        return dict(flatten_json(data))
    if suffix == ".csv":
        return csv_numeric_map(path)
    raise SystemExit(f"unsupported-file-type:{suffix}")


def compare_maps(exp: Dict[str, float], act: Dict[str, float], rtol: float, atol: float) -> Dict[str, Any]:
    keys = sorted(set(exp.keys()) & set(act.keys()))
    if not keys:
        return {
            "status": "fail",
            "compared_values": 0,
            "mismatch_count": 0,
            "max_rel_diff": None,
            "details": ["no-overlapping-numeric-values"],
        }

    mismatch = 0
    max_rel = 0.0
    details = []

    for k in keys:
        ev = exp[k]
        av = act[k]
        abs_diff = abs(ev - av)
        denom = max(abs(ev), abs(av), 1e-30)
        rel = abs_diff / denom
        max_rel = max(max_rel, rel)
        if abs_diff > (atol + rtol * abs(ev)):
            mismatch += 1
            if len(details) < 20:
                details.append(f"{k}: exp={ev} act={av} rel={rel:.3e}")

    compared = len(keys)
    ratio = mismatch / compared
    if mismatch == 0:
        status = "match"
    elif ratio <= 0.05:
        status = "partial"
    else:
        status = "fail"

    return {
        "status": status,
        "compared_values": compared,
        "mismatch_count": mismatch,
        "max_rel_diff": max_rel,
        "details": details,
    }


def main() -> int:
    args = parse_args()
    exp_path = Path(args.expected)
    act_path = Path(args.actual)

    exp = load_numeric_map(exp_path)
    act = load_numeric_map(act_path)
    result = compare_maps(exp, act, args.rtol, args.atol)

    report = {
        "expected": str(exp_path),
        "actual": str(act_path),
        "rtol": args.rtol,
        "atol": args.atol,
        **result,
    }

    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2), encoding="utf-8")

    print(f"wrote={out} status={report['status']} mismatches={report['mismatch_count']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
