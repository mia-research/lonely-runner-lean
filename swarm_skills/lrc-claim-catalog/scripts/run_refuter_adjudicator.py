#!/usr/bin/env python3
"""Deterministic refuter/adjudicator pass for extracted claims.

Prioritizes P1 items first and emits a scored adjudication table.
"""

from __future__ import annotations

import argparse
import csv
import re
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Tuple

PRIORITY_RANK = {
    "P1_core_proof_or_primary_evidence": 1,
    "P2_supporting_or_replication": 2,
    "P3_context_or_auxiliary": 3,
}

BASE_SCORE = {
    "theorem_claim": 0.52,
    "empirical_claim": 0.48,
    "conjecture": 0.40,
    "candidate_claim": 0.35,
}

THEOREM_TERMS = {
    "theorem",
    "proof",
    "lemma",
    "proposition",
    "corollary",
    "qed",
    "therefore",
}

EMPIRICAL_TERMS = {
    "experiment",
    "numerical",
    "simulation",
    "benchmark",
    "dataset",
    "computed",
    "table",
    "error",
    "runtime",
}

CONJECTURE_TERMS = {
    "conjecture",
    "open",
    "unresolved",
    "hypothesis",
}

QUANTIFIER_TERMS = {
    "for all",
    "there exists",
    "if and only if",
    "forall",
    "exists",
}

UNCERTAINTY_TERMS = {
    "might",
    "could",
    "possibly",
    "seems",
    "likely",
    "draft",
    "tentative",
}


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Run deterministic refuter/adjudicator pass")
    p.add_argument("--input", required=True, help="Path to registry/claims.csv")
    p.add_argument("--output", required=True, help="Path to adjudication CSV output")
    p.add_argument("--summary", required=True, help="Path to markdown summary output")
    return p.parse_args()


def priority_rank(priority: str) -> int:
    return PRIORITY_RANK.get((priority or "").strip(), 9)


def normalized_text(row: Dict[str, str]) -> str:
    parts = [
        row.get("short_statement", ""),
        row.get("assumptions", ""),
        row.get("source_excerpt", ""),
        row.get("filename", ""),
    ]
    return " ".join(parts).lower()


def count_terms(text: str, terms: set[str]) -> int:
    return sum(1 for t in terms if t in text)


def has_quantifier(text: str) -> bool:
    return any(t in text for t in QUANTIFIER_TERMS)


def tokenize_reason_codes(*codes: str) -> str:
    seen = []
    for c in codes:
        if c and c not in seen:
            seen.append(c)
    return "|".join(seen)


def adjudicate_row(row: Dict[str, str]) -> Dict[str, str]:
    claim_type = (row.get("claim_type") or "candidate_claim").strip()
    extraction_method = (row.get("extraction_method") or "").strip()
    excerpt = row.get("source_excerpt", "") or ""
    text = normalized_text(row)

    theorem_hits = count_terms(text, THEOREM_TERMS)
    empirical_hits = count_terms(text, EMPIRICAL_TERMS)
    conjecture_hits = count_terms(text, CONJECTURE_TERMS)
    uncertainty_hits = count_terms(text, UNCERTAINTY_TERMS)
    quantifier = has_quantifier(text)

    score = BASE_SCORE.get(claim_type, 0.35)
    reason_codes: List[str] = []

    if theorem_hits >= 2:
        score += 0.15
        reason_codes.append("theorem_signals")
    if empirical_hits >= 2:
        score += 0.12
        reason_codes.append("empirical_signals")
    if conjecture_hits >= 1 and claim_type == "conjecture":
        score += 0.08
        reason_codes.append("conjecture_context")
    if quantifier:
        score += 0.10
        reason_codes.append("formal_quantifier")
    if uncertainty_hits > 0:
        score -= 0.18
        reason_codes.append("uncertainty_language")
    if extraction_method == "filename_only_pdf":
        score -= 0.22
        reason_codes.append("insufficient_text_extraction")
    if len(excerpt.strip()) < 80:
        score -= 0.12
        reason_codes.append("short_excerpt")

    score = max(0.0, min(score, 0.99))

    if score >= 0.75:
        tier = "A-Strong"
    elif score >= 0.62:
        tier = "B-Promising"
    elif score >= 0.50:
        tier = "C-Weak"
    else:
        tier = "D-Insufficient"

    if extraction_method == "filename_only_pdf" or score < 0.45:
        decision = "hold_insufficient_extraction"
        runtime = "5"
    elif claim_type == "empirical_claim" and score >= 0.56:
        decision = "promote_numeric_test"
        runtime = "20"
    elif claim_type == "theorem_claim" and score >= 0.62:
        decision = "promote_formal_refutation"
        runtime = "45"
    elif claim_type == "conjecture" and score >= 0.56:
        decision = "promote_counterexample_search"
        runtime = "25"
    else:
        decision = "needs_human_review"
        runtime = "15"

    return {
        "claim_id": row.get("claim_id", ""),
        "source_artifact_id": row.get("source_artifact_id", ""),
        "priority_note": row.get("priority_note", ""),
        "priority_rank": str(priority_rank(row.get("priority_note", ""))),
        "claim_type": claim_type,
        "status_in": row.get("status", ""),
        "adjudication_score": f"{score:.3f}",
        "adjudication_tier": tier,
        "decision": decision,
        "reason_codes": tokenize_reason_codes(*reason_codes),
        "file_type": row.get("file_type", ""),
        "source_path": row.get("source_path", ""),
        "runtime_estimate_min": runtime,
        "created_utc": datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
    }


def sort_key(row: Dict[str, str]) -> Tuple[int, str]:
    return (priority_rank(row.get("priority_note", "")), row.get("claim_id", ""))


def write_summary(
    summary_path: Path,
    rows: List[Dict[str, str]],
) -> None:
    decision_counts = Counter(r["decision"] for r in rows)
    tier_counts = Counter(r["adjudication_tier"] for r in rows)
    p1_rows = [r for r in rows if r["priority_rank"] == "1"]
    p1_decisions = Counter(r["decision"] for r in p1_rows)

    lines = [
        "# Refuter/Adjudicator Summary",
        "",
        f"Generated: {datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace('+00:00', 'Z')}",
        "",
        "## Core Metrics",
        f"- claims_processed: {len(rows)}",
        f"- p1_processed_first: {len(p1_rows)}",
        "",
        "## Decision Counts",
    ]
    for k, v in sorted(decision_counts.items()):
        lines.append(f"- {k}: {v}")

    lines += ["", "## Tier Counts"]
    for k, v in sorted(tier_counts.items()):
        lines.append(f"- {k}: {v}")

    lines += ["", "## P1 Decision Counts"]
    for k, v in sorted(p1_decisions.items()):
        lines.append(f"- {k}: {v}")

    summary_path.parent.mkdir(parents=True, exist_ok=True)
    summary_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    in_path = Path(args.input)
    out_path = Path(args.output)
    summary_path = Path(args.summary)

    with in_path.open(newline="", encoding="utf-8") as f:
        claims = list(csv.DictReader(f))

    claims_sorted = sorted(claims, key=sort_key)
    adjudicated = [adjudicate_row(r) for r in claims_sorted]

    out_path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "claim_id",
        "source_artifact_id",
        "priority_note",
        "priority_rank",
        "claim_type",
        "status_in",
        "adjudication_score",
        "adjudication_tier",
        "decision",
        "reason_codes",
        "file_type",
        "source_path",
        "runtime_estimate_min",
        "created_utc",
    ]
    with out_path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(adjudicated)

    write_summary(summary_path, adjudicated)
    print(f"wrote_adjudication={out_path} rows={len(adjudicated)}")
    print(f"wrote_summary={summary_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
