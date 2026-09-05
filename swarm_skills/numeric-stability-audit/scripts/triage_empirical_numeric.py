#!/usr/bin/env python3
"""Numeric-stability triage for empirical claims.

This pass identifies floating-point risk and emits precision-ladder run plans.
"""

from __future__ import annotations

import argparse
import csv
import re
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List

DECIMAL_RE = re.compile(r"(?<![A-Za-z0-9_])[-+]?\d+\.\d+(?:[eE][-+]?\d+)?")
EXP_RE = re.compile(r"(?<![A-Za-z0-9_])[-+]?\d+(?:\.\d+)?[eE][-+]?\d+")

HIGH_RISK_TERMS = {
    "float",
    "rounding",
    "tolerance",
    "approx",
    "approximate",
    "unstable",
    "catastrophic",
    "cancellation",
    "underflow",
    "overflow",
}

MEDIUM_RISK_TERMS = {
    "decimal",
    "precision",
    "error",
    "residual",
    "threshold",
    "epsilon",
    "sigma",
}

REPRO_TERMS = {
    "seed",
    "deterministic",
    "reproducible",
    "fixed seed",
    "exact",
    "rational",
}


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Triages empirical claims for numeric stability")
    p.add_argument("--input", required=True, help="Input empirical claims CSV")
    p.add_argument("--output", required=True, help="Output numeric triage CSV")
    p.add_argument("--summary", required=True, help="Summary markdown")
    return p.parse_args()


def row_text(row: Dict[str, str]) -> str:
    return " ".join(
        [
            row.get("short_statement", ""),
            row.get("assumptions", ""),
            row.get("source_excerpt", ""),
            row.get("filename", ""),
        ]
    ).lower()


def classify_risk(text: str, number_count: int) -> str:
    high_hits = sum(1 for t in HIGH_RISK_TERMS if t in text)
    med_hits = sum(1 for t in MEDIUM_RISK_TERMS if t in text)

    if high_hits >= 2:
        return "high"
    if high_hits >= 1 and number_count >= 4:
        return "high"
    if med_hits >= 2 or number_count >= 6:
        return "medium"
    return "low"


def plan_for_risk(risk: str) -> str:
    if risk == "high":
        return "binary64_vs_decimal128_vs_mpmath200"
    if risk == "medium":
        return "binary64_vs_decimal128"
    return "binary64_sanity_replay"


def runtime_for_risk(risk: str) -> str:
    return {"high": "30", "medium": "18", "low": "10"}[risk]


def stable_threshold_for_risk(risk: str) -> str:
    return {"high": "1e-11", "medium": "1e-9", "low": "1e-8"}[risk]


def sensitive_threshold_for_risk(risk: str) -> str:
    return {"high": "1e-7", "medium": "1e-6", "low": "1e-5"}[risk]


def main() -> int:
    args = parse_args()
    in_path = Path(args.input)
    out_path = Path(args.output)
    summary_path = Path(args.summary)

    with in_path.open(newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))

    triaged: List[Dict[str, str]] = []
    for r in rows:
        text = row_text(r)
        decimals = DECIMAL_RE.findall(text)
        exps = EXP_RE.findall(text)
        number_count = len(decimals) + len(exps)
        repro_hits = sum(1 for t in REPRO_TERMS if t in text)
        risk = classify_risk(text, number_count)

        needs_precision = "yes" if (risk in {"high", "medium"} or number_count >= 2) else "no"
        confidence = "0.82" if risk == "high" else "0.72" if risk == "medium" else "0.60"

        triaged.append(
            {
                "claim_id": r.get("claim_id", ""),
                "priority_note": r.get("priority_note", ""),
                "numeric_literals_detected": str(number_count),
                "repro_markers_detected": str(repro_hits),
                "float_risk": risk,
                "needs_precision_ladder": needs_precision,
                "precision_plan": plan_for_risk(risk),
                "stable_threshold": stable_threshold_for_risk(risk),
                "sensitive_threshold": sensitive_threshold_for_risk(risk),
                "runtime_estimate_min": runtime_for_risk(risk),
                "confidence": confidence,
                "created_utc": datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
            }
        )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "claim_id",
        "priority_note",
        "numeric_literals_detected",
        "repro_markers_detected",
        "float_risk",
        "needs_precision_ladder",
        "precision_plan",
        "stable_threshold",
        "sensitive_threshold",
        "runtime_estimate_min",
        "confidence",
        "created_utc",
    ]
    with out_path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(triaged)

    risk_counts = Counter(x["float_risk"] for x in triaged)
    ladder_yes = sum(1 for x in triaged if x["needs_precision_ladder"] == "yes")

    lines = [
        "# Numeric Stability Triage Summary",
        "",
        f"Generated: {datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace('+00:00', 'Z')}",
        "",
        "## Core Metrics",
        f"- empirical_claims_processed: {len(triaged)}",
        f"- precision_ladder_required: {ladder_yes}",
        "",
        "## Risk Counts",
    ]
    for k, v in sorted(risk_counts.items()):
        lines.append(f"- {k}: {v}")

    summary_path.parent.mkdir(parents=True, exist_ok=True)
    summary_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"wrote_triage={out_path} rows={len(triaged)}")
    print(f"wrote_summary={summary_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
