#!/usr/bin/env python3
"""Build promotion queue for strongest claims into reproducible local tests."""

from __future__ import annotations

import argparse
import csv
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Tuple

PRIORITY_RANK = {
    "P1_core_proof_or_primary_evidence": 1,
    "P2_supporting_or_replication": 2,
    "P3_context_or_auxiliary": 3,
}


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Build promotion queue from adjudication and audits")
    p.add_argument("--claims", required=True, help="registry/claims.csv")
    p.add_argument("--adjudication", required=True, help="reports adjudication csv")
    p.add_argument("--measurement-audit", required=True, help="notation/measurement audit on empirical claims")
    p.add_argument("--numeric-triage", required=True, help="numeric triage csv")
    p.add_argument("--output", required=True, help="queue csv output")
    p.add_argument("--summary", required=True, help="summary markdown output")
    p.add_argument("--max-items", type=int, default=30)
    return p.parse_args()


def load_csv_map(path: Path, key: str) -> Dict[str, Dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    out: Dict[str, Dict[str, str]] = {}
    for r in rows:
        k = r.get(key, "")
        if k:
            out[k] = r
    return out


def parse_float(s: str, default: float = 0.0) -> float:
    try:
        return float(s)
    except (TypeError, ValueError):
        return default


def priority_rank(priority: str) -> int:
    return PRIORITY_RANK.get((priority or "").strip(), 9)


def promotion_track(decision: str, claim_type: str) -> str:
    if decision == "promote_numeric_test":
        return "numeric_test"
    if decision == "promote_formal_refutation":
        return "formal_refutation"
    if decision == "promote_counterexample_search":
        return "counterexample_search"
    if claim_type == "empirical_claim":
        return "numeric_test"
    return "formal_refutation"


def required_checks(track: str, metric_match: str, notation_match: str, float_risk: str) -> str:
    checks = ["changelog_entry", "artifact_hash"]
    if metric_match != "pass":
        checks.append("metric_alignment_review")
    if notation_match != "pass":
        checks.append("notation_fix_required")
    if track == "numeric_test":
        checks.append("precision_ladder")
        checks.append("independent_repro")
        if float_risk == "high":
            checks.append("decimal_or_mpmath_crosscheck")
    else:
        checks.append("symbolic_consistency_check")
    return "|".join(checks)


def score_row(adj: Dict[str, str], metric_match: str, notation_match: str, float_risk: str) -> float:
    score = parse_float(adj.get("adjudication_score", "0"), 0.0)
    if metric_match == "pass":
        score += 0.08
    elif metric_match == "partial":
        score += 0.03
    else:
        score -= 0.05

    if notation_match == "pass":
        score += 0.07
    elif notation_match == "partial":
        score += 0.02
    else:
        score -= 0.06

    if float_risk == "low":
        score += 0.03
    elif float_risk == "high":
        score -= 0.04

    return max(0.0, min(score, 0.99))


def runtime_estimate(track: str, base_runtime: str, triage_runtime: str) -> str:
    base = parse_float(base_runtime, 15.0)
    tri = parse_float(triage_runtime, 0.0)
    if track == "numeric_test":
        total = max(base, tri + 8)
    elif track == "counterexample_search":
        total = max(base, 22.0)
    else:
        total = max(base, 35.0)
    return str(int(round(total)))


def main() -> int:
    args = parse_args()

    claims = load_csv_map(Path(args.claims), "claim_id")
    adjud = load_csv_map(Path(args.adjudication), "claim_id")
    meas = load_csv_map(Path(args.measurement_audit), "claim_id")
    triage = load_csv_map(Path(args.numeric_triage), "claim_id")

    eligible_decisions = {
        "promote_numeric_test",
        "promote_formal_refutation",
        "promote_counterexample_search",
    }

    candidates: List[Dict[str, str]] = []
    for claim_id, a in adjud.items():
        decision = a.get("decision", "")

        c = claims.get(claim_id, {})
        claim_type = c.get("claim_type", a.get("claim_type", "candidate_claim"))

        m = meas.get(claim_id, {})
        t = triage.get(claim_id, {})

        metric_match = m.get("metric_match", "unknown")
        notation_match = m.get("notation_match", "unknown")
        float_risk = t.get("float_risk", "unknown")
        needs_ladder = t.get("needs_precision_ladder", "no")
        adj_score = parse_float(a.get("adjudication_score", "0"), 0.0)

        # Hard guard: do not auto-promote contradictory metric/notation failures.
        if metric_match == "fail" or notation_match == "fail":
            continue

        is_direct_promotion = decision in eligible_decisions
        is_empirical_fallback = (
            not is_direct_promotion
            and claim_type == "empirical_claim"
            and metric_match in {"pass", "partial"}
            and notation_match == "pass"
            and needs_ladder == "yes"
            and adj_score >= 0.45
        )
        if not (is_direct_promotion or is_empirical_fallback):
            continue

        if is_empirical_fallback:
            decision_source = "promote_numeric_test_from_audit"
            promotion_basis = "audit_fallback"
            track = "numeric_test"
        else:
            decision_source = decision
            promotion_basis = "direct"
            track = promotion_track(decision, claim_type)

        composite = score_row(a, metric_match, notation_match, float_risk)
        if is_empirical_fallback:
            composite = min(0.99, max(composite, 0.50) + 0.02)

        candidates.append(
            {
                "claim_id": claim_id,
                "priority_note": a.get("priority_note", c.get("priority_note", "")),
                "priority_rank": str(priority_rank(a.get("priority_note", c.get("priority_note", "")))),
                "claim_type": claim_type,
                "promotion_track": track,
                "decision_source": decision_source,
                "promotion_basis": promotion_basis,
                "composite_score": f"{composite:.3f}",
                "required_checks": required_checks(track, metric_match, notation_match, float_risk),
                "metric_match": metric_match,
                "notation_match": notation_match,
                "float_risk": float_risk,
                "source_path": a.get("source_path", c.get("source_path", "")),
                "runtime_estimate_min": runtime_estimate(
                    track,
                    a.get("runtime_estimate_min", "15"),
                    t.get("runtime_estimate_min", "0"),
                ),
            }
        )

    candidates.sort(
        key=lambda r: (
            int(r["priority_rank"]),
            -parse_float(r["composite_score"], 0.0),
            r["claim_id"],
        )
    )
    top = candidates[: args.max_items]

    out_rows: List[Dict[str, str]] = []
    ts = datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    for idx, row in enumerate(top, start=1):
        out_rows.append(
            {
                "promotion_id": f"PROMO-LRC-{idx:04d}",
                **row,
                "owner": "local_python",
                "queue_status": "queued",
                "created_utc": ts,
            }
        )

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "promotion_id",
        "claim_id",
        "priority_note",
        "priority_rank",
        "claim_type",
        "promotion_track",
        "decision_source",
        "promotion_basis",
        "composite_score",
        "required_checks",
        "metric_match",
        "notation_match",
        "float_risk",
        "source_path",
        "runtime_estimate_min",
        "owner",
        "queue_status",
        "created_utc",
    ]
    with out_path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(out_rows)

    track_counts = Counter(r["promotion_track"] for r in out_rows)
    basis_counts = Counter(r["promotion_basis"] for r in out_rows)
    p1_count = sum(1 for r in out_rows if r["priority_rank"] == "1")

    summary_lines = [
        "# Promotion Queue Summary",
        "",
        f"Generated: {ts}",
        "",
        "## Core Metrics",
        f"- candidates_seen: {len(candidates)}",
        f"- queue_written: {len(out_rows)}",
        f"- p1_in_queue: {p1_count}",
        "",
        "## Track Counts",
    ]
    for k, v in sorted(track_counts.items()):
        summary_lines.append(f"- {k}: {v}")
    summary_lines += ["", "## Basis Counts"]
    for k, v in sorted(basis_counts.items()):
        summary_lines.append(f"- {k}: {v}")

    summary_path = Path(args.summary)
    summary_path.parent.mkdir(parents=True, exist_ok=True)
    summary_path.write_text("\n".join(summary_lines) + "\n", encoding="utf-8")

    print(f"wrote_queue={out_path} rows={len(out_rows)}")
    print(f"wrote_summary={summary_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
