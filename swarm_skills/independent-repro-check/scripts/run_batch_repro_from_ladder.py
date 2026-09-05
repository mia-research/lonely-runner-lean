#!/usr/bin/env python3
"""Batch repro check using precision ladder artifacts.

For each promoted claim, this script:
1. Reads compare_float64_vs_mpmath.csv (baseline = float64 computation)
2. Reads compare_decimal128_vs_mpmath.csv (baseline = decimal128 computation)
3. Extracts key metrics (excluding epsilon_probe diagnostic and summary rows)
4. Creates expected (float64 baselines) and actual (decimal128 baselines) JSON artifacts
5. Runs repro_compare.py to generate a match/partial/fail decision
6. Writes per-claim report and a batch summary

Usage:
    python3 run_batch_repro_from_ladder.py \
        --repro-root <reports/repro/cycle_002/> \
        --claims-csv <registry/claim_status_registry.csv> \
        --output-root <reports/repro/batch_repro_cycle_002/> \
        --summary-csv <reports/repro/batch_repro_cycle_002_summary.csv> \
        --summary-md  <reports/repro/batch_repro_cycle_002_summary.md>
"""
from __future__ import annotations

import argparse
import csv
import json
import subprocess
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List

EXCLUDE_METRICS = {"epsilon_probe", "GLOBAL_STATUS", "MAX_REL_DIFF"}


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Batch repro check from precision ladder artifacts")
    p.add_argument("--repro-root", required=True, help="Root dir containing per-claim repro directories")
    p.add_argument("--claims-csv", required=True, help="Claim status registry CSV (for claim IDs)")
    p.add_argument("--output-root", required=True, help="Root dir for per-claim repro report output")
    p.add_argument("--summary-csv", required=True, help="Output batch summary CSV")
    p.add_argument("--summary-md", required=True, help="Output batch summary markdown")
    p.add_argument("--rtol", type=float, default=1e-7)
    p.add_argument("--atol", type=float, default=1e-10)
    return p.parse_args()


def read_csv(path: Path) -> List[Dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def write_csv(path: Path, rows: List[Dict], fieldnames=None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    if fieldnames is None:
        seen: List[str] = []
        for r in rows:
            for k in r:
                if k not in seen:
                    seen.append(k)
        fieldnames = seen
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)


def extract_metrics(csv_path: Path) -> Dict[str, float]:
    """Extract baseline numeric values from a ladder CSV, excluding diagnostic rows."""
    out: Dict[str, float] = {}
    if not csv_path.exists():
        return out
    rows = read_csv(csv_path)
    for row in rows:
        metric = (row.get("metric") or "").strip()
        if metric in EXCLUDE_METRICS or not metric:
            continue
        baseline = (row.get("baseline") or "").strip()
        try:
            out[metric] = float(baseline)
        except ValueError:
            pass
    return out


def main() -> int:
    args = parse_args()

    claims_rows = read_csv(Path(args.claims_csv))
    claim_ids = [r["claim_id"].strip() for r in claims_rows if r.get("claim_id", "").strip()]

    repro_root = Path(args.repro_root)
    out_root = Path(args.output_root)

    this_script = Path(__file__).resolve()
    repro_compare = this_script.parent / "repro_compare.py"

    summary_rows: List[Dict] = []

    for claim_id in claim_ids:
        claim_dir = repro_root / claim_id
        float64_csv = claim_dir / "compare_float64_vs_mpmath.csv"
        dec128_csv = claim_dir / "compare_decimal128_vs_mpmath.csv"

        if not float64_csv.exists() or not dec128_csv.exists():
            summary_rows.append({
                "claim_id": claim_id,
                "repro_status": "skip_missing_artifacts",
                "compared_values": 0,
                "mismatch_count": 0,
                "max_rel_diff": "",
                "note": f"missing: {'float64' if not float64_csv.exists() else 'decimal128'}",
                "generated_utc": utc_now(),
            })
            continue

        float64_metrics = extract_metrics(float64_csv)
        dec128_metrics = extract_metrics(dec128_csv)

        if not float64_metrics or not dec128_metrics:
            summary_rows.append({
                "claim_id": claim_id,
                "repro_status": "skip_no_numeric_metrics",
                "compared_values": 0,
                "mismatch_count": 0,
                "max_rel_diff": "",
                "note": "no numeric metrics extracted",
                "generated_utc": utc_now(),
            })
            continue

        # Write expected/actual JSON for repro_compare.py
        claim_out = out_root / claim_id
        claim_out.mkdir(parents=True, exist_ok=True)
        expected_path = claim_out / "expected_float64_baselines.json"
        actual_path = claim_out / "actual_decimal128_baselines.json"
        report_path = claim_out / "repro_report.json"

        expected_path.write_text(json.dumps(float64_metrics, indent=2), encoding="utf-8")
        actual_path.write_text(json.dumps(dec128_metrics, indent=2), encoding="utf-8")

        cmd = [
            sys.executable,
            str(repro_compare),
            "--expected", str(expected_path),
            "--actual", str(actual_path),
            "--output", str(report_path),
            "--rtol", str(args.rtol),
            "--atol", str(args.atol),
        ]
        result = subprocess.run(cmd, capture_output=True, text=True)

        if result.returncode != 0:
            summary_rows.append({
                "claim_id": claim_id,
                "repro_status": "error",
                "compared_values": 0,
                "mismatch_count": 0,
                "max_rel_diff": "",
                "note": result.stderr.strip()[-200:],
                "generated_utc": utc_now(),
            })
            continue

        try:
            report = json.loads(report_path.read_text(encoding="utf-8"))
        except Exception as e:
            summary_rows.append({
                "claim_id": claim_id,
                "repro_status": "error",
                "compared_values": 0,
                "mismatch_count": 0,
                "max_rel_diff": "",
                "note": f"json_parse_error:{e}",
                "generated_utc": utc_now(),
            })
            continue

        summary_rows.append({
            "claim_id": claim_id,
            "repro_status": report.get("status", ""),
            "compared_values": report.get("compared_values", 0),
            "mismatch_count": report.get("mismatch_count", 0),
            "max_rel_diff": str(report.get("max_rel_diff", "")),
            "note": "|".join(report.get("details", []))[:200],
            "generated_utc": utc_now(),
        })

    write_csv(
        Path(args.summary_csv),
        summary_rows,
        fieldnames=["claim_id", "repro_status", "compared_values", "mismatch_count", "max_rel_diff", "note", "generated_utc"],
    )

    status_counts = Counter(r["repro_status"] for r in summary_rows)

    lines = [
        "# Batch Independent Repro Check Summary",
        "",
        f"Generated: {utc_now()}",
        f"Claims processed: {len(summary_rows)}",
        f"Method: float64_baseline vs decimal128_baseline (key metrics, epsilon_probe excluded)",
        f"rtol: {args.rtol}  atol: {args.atol}",
        "",
        "## Status Counts",
    ]
    for k, v in sorted(status_counts.items()):
        lines.append(f"- {k}: {v}")
    lines += [
        "",
        "## Per-Claim Results",
        "| Claim | Status | Compared | Mismatches | Max Rel Diff |",
        "|---|---|---|---|---|",
    ]
    for r in summary_rows:
        lines.append(
            f"| {r['claim_id']} | {r['repro_status']} | {r['compared_values']} | {r['mismatch_count']} | {r['max_rel_diff']} |"
        )

    md_path = Path(args.summary_md)
    md_path.parent.mkdir(parents=True, exist_ok=True)
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"wrote_summary_csv={args.summary_csv} rows={len(summary_rows)}")
    print(f"wrote_summary_md={args.summary_md}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
