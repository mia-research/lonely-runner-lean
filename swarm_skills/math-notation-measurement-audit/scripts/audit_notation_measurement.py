#!/usr/bin/env python3
"""Template audit for notation drift and metric alignment."""

from __future__ import annotations

import argparse
import csv
import re
from pathlib import Path
from typing import Dict, Iterable, List

SYMBOL_ALIAS_GROUPS = [
    {"phi", "varphi", "φ"},
    {"zeta", "ζ"},
    {"sigma", "σ"},
    {"delta", "Δ", "δ"},
]

METRIC_GROUPS = {
    "individual_isolation": {"individual isolation", "pointwise isolation"},
    "global_isolation": {"global isolation", "aggregate isolation"},
    "boundary_events": {"boundary", "event-complete", "threshold"},
    "alignment": {"alignment", "phase alignment", "coherence"},
}

TEXT_FIELDS = [
    "short_statement",
    "claim_text",
    "metric_definition",
    "experiment_metric",
    "notes",
    "filename",
]


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Audit notation and measurement consistency")
    p.add_argument("--input", required=True, help="Input CSV")
    p.add_argument("--output", required=True, help="Output CSV")
    return p.parse_args()


def row_text(row: Dict[str, str]) -> str:
    return " ".join((row.get(k, "") or "") for k in TEXT_FIELDS).lower()


def detect_alias_conflicts(text: str) -> List[str]:
    issues: List[str] = []
    for group in SYMBOL_ALIAS_GROUPS:
        present = sorted([s for s in group if s in text])
        if len(present) > 1:
            issues.append(f"alias-mix:{'/'.join(present)}")
    return issues


def detect_overloaded_symbols(text: str) -> List[str]:
    issues: List[str] = []
    # Simple heuristic: repeated declaration patterns for same symbol.
    for sym in ["phi", "sigma", "delta", "zeta", "n", "k"]:
        decls = re.findall(rf"\b{sym}\b\s*(?:=|:)", text)
        if len(decls) >= 2:
            issues.append(f"possible-overload:{sym}")
    return issues


def metric_profile(text: str) -> List[str]:
    found: List[str] = []
    for key, terms in METRIC_GROUPS.items():
        if any(t in text for t in terms):
            found.append(key)
    return sorted(found)


def evaluate_metric_match(text: str) -> str:
    prof = metric_profile(text)
    if not prof:
        return "partial"
    # If contradictory families appear together, fail.
    if "individual_isolation" in prof and "global_isolation" in prof:
        return "fail"
    return "pass"


def evaluate_notation_match(issues: Iterable[str]) -> str:
    issues = list(issues)
    if not issues:
        return "pass"
    if any(i.startswith("possible-overload") for i in issues):
        return "fail"
    return "partial"


def main() -> int:
    args = parse_args()
    in_path = Path(args.input)
    out_path = Path(args.output)

    with in_path.open(newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow([
            "claim_id",
            "notation_match",
            "metric_match",
            "issues",
            "required_fixes",
            "numeric_escalation",
            "confidence",
        ])

        for r in rows:
            cid = r.get("claim_id") or r.get("source_artifact_id") or "UNKNOWN"
            txt = row_text(r)
            issues = detect_alias_conflicts(txt) + detect_overloaded_symbols(txt)
            n_match = evaluate_notation_match(issues)
            m_match = evaluate_metric_match(txt)
            escalate = "yes" if any(term in txt for term in ["float", "tolerance", "precision", "rounding"]) else "no"

            fixes = []
            if n_match != "pass":
                fixes.append("add_symbol_map")
            if m_match != "pass":
                fixes.append("align_metric_definition")

            if n_match == "pass" and m_match == "pass":
                conf = "0.85"
            elif "fail" in {n_match, m_match}:
                conf = "0.90"
            else:
                conf = "0.65"

            w.writerow([
                cid,
                n_match,
                m_match,
                "|".join(issues),
                "|".join(fixes),
                escalate,
                conf,
            ])

    print(f"wrote={out_path} rows={len(rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
