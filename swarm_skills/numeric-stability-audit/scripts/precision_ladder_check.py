#!/usr/bin/env python3
"""Compare baseline vs high-precision numeric JSON outputs."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Any, Dict, List, Tuple


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Precision ladder check")
    p.add_argument("--baseline", required=True, help="Baseline JSON")
    p.add_argument("--high", required=True, help="High-precision JSON")
    p.add_argument("--output", required=True, help="Output CSV report")
    p.add_argument("--stable-threshold", type=float, default=1e-9)
    p.add_argument("--sensitive-threshold", type=float, default=1e-5)
    return p.parse_args()


def flatten(obj: Any, prefix: str = "") -> List[Tuple[str, float]]:
    out: List[Tuple[str, float]] = []
    if isinstance(obj, dict):
        for k in sorted(obj.keys()):
            key = f"{prefix}.{k}" if prefix else str(k)
            out.extend(flatten(obj[k], key))
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            key = f"{prefix}[{i}]"
            out.extend(flatten(v, key))
    elif isinstance(obj, (int, float)):
        out.append((prefix, float(obj)))
    return out


def status_for(rel_diff: float, stable: float, sensitive: float) -> str:
    if rel_diff <= stable:
        return "stable"
    if rel_diff <= sensitive:
        return "precision_sensitive"
    return "unstable"


def main() -> int:
    args = parse_args()
    b = json.loads(Path(args.baseline).read_text(encoding="utf-8"))
    h = json.loads(Path(args.high).read_text(encoding="utf-8"))

    b_map = dict(flatten(b))
    h_map = dict(flatten(h))

    keys = sorted(set(b_map.keys()) & set(h_map.keys()))
    if not keys:
        raise SystemExit("no-overlapping-numeric-keys")

    rows = []
    worst = 0.0
    for k in keys:
        bv = b_map[k]
        hv = h_map[k]
        abs_diff = abs(bv - hv)
        denom = max(abs(bv), abs(hv), 1e-30)
        rel_diff = abs_diff / denom
        worst = max(worst, rel_diff)
        rows.append((k, bv, hv, abs_diff, rel_diff, status_for(rel_diff, args.stable_threshold, args.sensitive_threshold)))

    global_status = status_for(worst, args.stable_threshold, args.sensitive_threshold)

    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["key", "baseline", "high_precision", "abs_diff", "rel_diff", "status"])
        for r in rows:
            w.writerow(r)
        w.writerow([])
        w.writerow(["GLOBAL_STATUS", global_status])
        w.writerow(["MAX_REL_DIFF", f"{worst:.12e}"])

    print(f"wrote={out} keys={len(keys)} global_status={global_status} max_rel_diff={worst:.3e}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
