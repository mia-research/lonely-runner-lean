#!/usr/bin/env python3
"""Execute focused measurement-fix tickets and update queue state.

This script resolves partial metric matches by generating canonical metric mappings
and running deterministic consistency checks per metric family.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Tuple


PCT_CI_RE = re.compile(r"(?P<pct>\d+(?:\.\d+)?)%\s*\[(?P<lo>\d+(?:\.\d+)?)-(?P<hi>\d+(?:\.\d+)?)%\]")
ALPHA_RE = re.compile(r"α\s*=\s*([0-9]*\.?[0-9]+)")


@dataclass
class TicketResult:
    fix_ticket_id: str
    claim_id: str
    status: str
    metric_match_out: str
    checks_passed: int
    checks_failed: int
    notes: str
    artifact_dir: str
    updated_utc: str


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Run measurement-fix tickets")
    p.add_argument("--tickets", required=True, help="Input measurement-fix queue CSV")
    p.add_argument("--queue", required=True, help="Input promotion queue CSV")
    p.add_argument("--claims", required=True, help="Input claims CSV")
    p.add_argument("--output-dir", required=True, help="Root directory for per-claim fix artifacts")
    p.add_argument("--results-csv", required=True, help="Measurement fix results CSV")
    p.add_argument("--results-md", required=True, help="Measurement fix results markdown")
    p.add_argument("--tickets-out", required=True, help="Output measurement-fix queue CSV with statuses")
    p.add_argument("--queue-out", required=True, help="Output promotion queue CSV with metric updates")
    return p.parse_args()


def read_csv(path: Path) -> List[Dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def write_csv(path: Path, rows: List[Dict[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    fieldnames: List[str] = []
    seen = set()
    for r in rows:
        for k in r.keys():
            if k not in seen:
                seen.add(k)
                fieldnames.append(k)
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)


def map_by(rows: List[Dict[str, str]], key: str) -> Dict[str, Dict[str, str]]:
    out: Dict[str, Dict[str, str]] = {}
    for r in rows:
        k = (r.get(key) or "").strip()
        if k:
            out[k] = r
    return out


def write_json(path: Path, obj: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2), encoding="utf-8")


def write_rows_csv(path: Path, rows: List[Dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    fieldnames = list(rows[0].keys())
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for r in rows:
            w.writerow(r)


def parse_p_value_cell(cell: str) -> Tuple[float | None, str]:
    c = (cell or "").strip()
    if not c or c.upper() == "N/A":
        return None, "na"
    if c.startswith("<"):
        try:
            return float(c[1:]), "lt"
        except ValueError:
            return None, "bad"
    if c.startswith("≤"):
        try:
            return float(c[1:]), "le"
        except ValueError:
            return None, "bad"
    try:
        return float(c), "eq"
    except ValueError:
        return None, "bad"


def run_general_pack(source_path: Path, artifact_dir: Path) -> Tuple[str, int, int, str]:
    text = source_path.read_text(encoding="utf-8", errors="replace")
    lines = [ln.rstrip("\n") for ln in text.splitlines()]

    alpha_match = ALPHA_RE.search(text)
    alpha = float(alpha_match.group(1)) if alpha_match else None

    parsed_rows: List[Dict[str, object]] = []
    checks_passed = 0
    checks_failed = 0

    # Parse success-rate table lines that contain repeated % [lo-hi%] patterns.
    for ln in lines:
        if "[" not in ln or "%" not in ln:
            continue
        m_all = list(PCT_CI_RE.finditer(ln))
        if len(m_all) < 2:
            continue
        label = ln.split("\t", 1)[0].strip() if "\t" in ln else ln.split(" ", 1)[0].strip()
        for i, m in enumerate(m_all, start=1):
            pct = float(m.group("pct"))
            lo = float(m.group("lo"))
            hi = float(m.group("hi"))
            parsed_rows.append(
                {
                    "row_label": label,
                    "horizon_idx": i,
                    "metric_name": "success_rate",
                    "metric_value_pct": pct,
                    "ci_low_pct": lo,
                    "ci_high_pct": hi,
                    "metric_unit": "percent",
                    "acceptance_threshold": ">=90pct",
                }
            )
            if 0.0 <= lo <= pct <= hi <= 100.0:
                checks_passed += 1
            else:
                checks_failed += 1

    if alpha is not None and 0.0 < alpha < 1.0:
        checks_passed += 1
    else:
        checks_failed += 1

    write_rows_csv(artifact_dir / "canonical_metrics.csv", parsed_rows)
    write_json(
        artifact_dir / "measurement_fix_report.json",
        {
            "family": "general_lrc_metric_pack",
            "alpha": alpha,
            "parsed_metric_rows": len(parsed_rows),
            "checks_passed": checks_passed,
            "checks_failed": checks_failed,
            "status": "resolved_pass" if checks_failed == 0 and parsed_rows else "needs_review",
        },
    )

    if checks_failed == 0 and parsed_rows:
        return "resolved_pass", checks_passed, checks_failed, "canonical_success_rate_table_extracted"
    return "needs_review", checks_passed, checks_failed, "insufficient_or_inconsistent_table_parse"


def run_residue_pack(
    source_path: Path,
    artifact_dir: Path,
    queue_row: Dict[str, str],
) -> Tuple[str, int, int, str]:
    obj = json.loads(source_path.read_text(encoding="utf-8"))
    tests = obj.get("tests", [])
    cop = None
    for t in tests:
        if t.get("name") == "coprime_residue_verification":
            cop = t
            break

    if not cop or not cop.get("results"):
        write_json(
            artifact_dir / "measurement_fix_report.json",
            {
                "family": "residue_error_pack",
                "status": "needs_review",
                "reason": "missing_coprime_residue_verification_results",
            },
        )
        return "needs_review", 0, 1, "missing_coprime_section"

    rows_out: List[Dict[str, object]] = []
    checks_passed = 0
    checks_failed = 0

    for r in cop["results"]:
        exp = sorted(r.get("expectedResidues", []))
        det = sorted(r.get("detectedResidues", []))
        calc_match = exp == det
        field_match = bool(r.get("perfectMatch", False))
        max_err = float(r.get("maxError", 0.0))
        avg_err = float(r.get("avgError", 0.0))

        invariant_ok = (calc_match == field_match) and (max_err >= avg_err >= 0.0)
        if invariant_ok:
            checks_passed += 1
        else:
            checks_failed += 1

        rows_out.append(
            {
                "n": r.get("n"),
                "phi_n": r.get("phi_n"),
                "metric_name": "residue_consistency",
                "perfect_match_recorded": field_match,
                "perfect_match_recomputed": calc_match,
                "max_error": max_err,
                "avg_error": avg_err,
                "metric_unit": "dimensionless",
                "acceptance_threshold": "max_error<=1e-12",
                "invariant_ok": invariant_ok,
            }
        )

    # Precision invariance check from executed precision ladder.
    rel_float = float(queue_row.get("ladder_max_rel_float_vs_mpmath") or 1.0)
    rel_dec = float(queue_row.get("ladder_max_rel_decimal_vs_mpmath") or 1.0)
    precision_ok = rel_float <= 1e-10 and rel_dec <= 1e-20
    if precision_ok:
        checks_passed += 1
    else:
        checks_failed += 1

    write_rows_csv(artifact_dir / "canonical_metrics.csv", rows_out)
    write_json(
        artifact_dir / "measurement_fix_report.json",
        {
            "family": "residue_error_pack",
            "rows": len(rows_out),
            "checks_passed": checks_passed,
            "checks_failed": checks_failed,
            "precision_invariance_ok": precision_ok,
            "max_rel_float_vs_mpmath": rel_float,
            "max_rel_decimal_vs_mpmath": rel_dec,
            "status": "resolved_pass" if checks_failed == 0 else "needs_review",
        },
    )

    if checks_failed == 0:
        return "resolved_pass", checks_passed, checks_failed, "residue_consistency_invariants_valid"
    return "needs_review", checks_passed, checks_failed, "residue_consistency_invariants_failed"


def run_statistical_pack(
    source_path: Path,
    artifact_dir: Path,
    queue_row: Dict[str, str],
) -> Tuple[str, int, int, str]:
    rows = []
    with source_path.open(newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        rows = list(reader)

    checks_passed = 0
    checks_failed = 0

    # Extract alpha from bonferroni row if present.
    alpha = None
    for r in rows:
        if (r.get("test_name") or "") == "multiple_comparisons":
            try:
                alpha = float(r.get("value") or "")
            except ValueError:
                alpha = None
    if alpha is None:
        alpha = 0.05

    canonical: List[Dict[str, object]] = []
    for r in rows:
        p_val, p_kind = parse_p_value_cell(r.get("p_value", ""))
        decision = "na"
        if p_val is not None:
            if p_kind in {"lt", "le"}:
                decision = "significant" if p_val <= alpha else "not_significant"
            else:
                decision = "significant" if p_val < alpha else "not_significant"

        # Consistency checks for numeric fields.
        row_ok = True
        val = (r.get("value") or "").strip()
        if val not in {"", "N/A"}:
            if val.startswith(">"):
                try:
                    float(val[1:])
                except ValueError:
                    row_ok = False
            else:
                try:
                    float(val)
                except ValueError:
                    row_ok = False
        if row_ok:
            checks_passed += 1
        else:
            checks_failed += 1

        canonical.append(
            {
                "test_name": r.get("test_name", ""),
                "statistic": r.get("statistic", ""),
                "metric_name": r.get("test_name", ""),
                "metric_value": r.get("value", ""),
                "p_value": r.get("p_value", ""),
                "alpha": alpha,
                "decision": decision,
                "effect_size": r.get("effect_size", ""),
                "confidence_interval": r.get("confidence_interval", ""),
                "sample_size": r.get("sample_size", ""),
                "metric_unit": "dimensionless",
            }
        )

    # Precision invariance gate.
    rel_float = float(queue_row.get("ladder_max_rel_float_vs_mpmath") or 1.0)
    rel_dec = float(queue_row.get("ladder_max_rel_decimal_vs_mpmath") or 1.0)
    precision_ok = rel_float <= 1e-10 and rel_dec <= 1e-20
    if precision_ok:
        checks_passed += 1
    else:
        checks_failed += 1

    write_rows_csv(artifact_dir / "canonical_metrics.csv", canonical)
    write_json(
        artifact_dir / "measurement_fix_report.json",
        {
            "family": "statistical_significance_pack",
            "alpha": alpha,
            "rows": len(canonical),
            "checks_passed": checks_passed,
            "checks_failed": checks_failed,
            "precision_invariance_ok": precision_ok,
            "max_rel_float_vs_mpmath": rel_float,
            "max_rel_decimal_vs_mpmath": rel_dec,
            "status": "resolved_pass" if checks_failed == 0 else "needs_review",
        },
    )

    if checks_failed == 0:
        return "resolved_pass", checks_passed, checks_failed, "statistical_schema_canonicalized"
    return "needs_review", checks_passed, checks_failed, "statistical_schema_inconsistency"


def execute_ticket(
    ticket: Dict[str, str],
    claim_map: Dict[str, Dict[str, str]],
    queue_map: Dict[str, Dict[str, str]],
    output_root: Path,
) -> TicketResult:
    claim_id = ticket.get("claim_id", "")
    fix_ticket_id = ticket.get("fix_ticket_id", "")
    family = ticket.get("detected_metric_family", "")

    claim = claim_map.get(claim_id, {})
    queue_row = queue_map.get(claim_id, {})
    source_path_str = ticket.get("source_path") or claim.get("source_path") or ""
    source_path = Path(source_path_str)

    artifact_dir = output_root / claim_id
    artifact_dir.mkdir(parents=True, exist_ok=True)

    if not source_path.exists():
        write_json(
            artifact_dir / "measurement_fix_report.json",
            {
                "status": "error",
                "reason": f"missing_source:{source_path}",
            },
        )
        return TicketResult(
            fix_ticket_id=fix_ticket_id,
            claim_id=claim_id,
            status="error",
            metric_match_out="partial",
            checks_passed=0,
            checks_failed=1,
            notes=f"missing_source:{source_path}",
            artifact_dir=str(artifact_dir),
            updated_utc=utc_now(),
        )

    if family == "general_lrc_metric_pack":
        status, passed, failed, notes = run_general_pack(source_path, artifact_dir)
    elif family == "residue_error_pack":
        status, passed, failed, notes = run_residue_pack(source_path, artifact_dir, queue_row)
    elif family == "statistical_significance_pack":
        status, passed, failed, notes = run_statistical_pack(source_path, artifact_dir, queue_row)
    else:
        write_json(
            artifact_dir / "measurement_fix_report.json",
            {
                "status": "error",
                "reason": f"unsupported_family:{family}",
            },
        )
        return TicketResult(
            fix_ticket_id=fix_ticket_id,
            claim_id=claim_id,
            status="error",
            metric_match_out="partial",
            checks_passed=0,
            checks_failed=1,
            notes=f"unsupported_family:{family}",
            artifact_dir=str(artifact_dir),
            updated_utc=utc_now(),
        )

    metric_match_out = "pass" if status == "resolved_pass" else "partial"
    return TicketResult(
        fix_ticket_id=fix_ticket_id,
        claim_id=claim_id,
        status=status,
        metric_match_out=metric_match_out,
        checks_passed=passed,
        checks_failed=failed,
        notes=notes,
        artifact_dir=str(artifact_dir),
        updated_utc=utc_now(),
    )


def main() -> int:
    args = parse_args()

    tickets_path = Path(args.tickets)
    queue_path = Path(args.queue)
    claims_path = Path(args.claims)
    output_root = Path(args.output_dir)

    tickets = read_csv(tickets_path)
    queue_rows = read_csv(queue_path)
    claims_rows = read_csv(claims_path)

    queue_map = map_by(queue_rows, "claim_id")
    claim_map = map_by(claims_rows, "claim_id")

    # Only execute queued tickets.
    queued = [t for t in tickets if (t.get("status") or "").strip() in {"queued", "retry"}]

    results: List[TicketResult] = []
    for t in queued:
        results.append(execute_ticket(t, claim_map, queue_map, output_root))

    result_map = {r.claim_id: r for r in results}

    # Update tickets.
    tickets_out: List[Dict[str, str]] = []
    for t in tickets:
        cid = t.get("claim_id", "")
        r = result_map.get(cid)
        row = dict(t)
        if r:
            row["status"] = r.status
            row["metric_match_out"] = r.metric_match_out
            row["checks_passed"] = str(r.checks_passed)
            row["checks_failed"] = str(r.checks_failed)
            row["artifact_dir"] = r.artifact_dir
            row["execution_notes"] = r.notes
            row["updated_utc"] = r.updated_utc
        tickets_out.append(row)

    # Update promotion queue metric match for resolved tickets.
    queue_out: List[Dict[str, str]] = []
    for q in queue_rows:
        cid = q.get("claim_id", "")
        r = result_map.get(cid)
        row = dict(q)
        if r and r.status == "resolved_pass":
            row["metric_match"] = "pass"
            row["required_checks"] = "|".join(
                sorted(
                    set(
                        [x for x in (row.get("required_checks", "") or "").split("|") if x]
                        + ["measurement_fix_resolved"]
                    )
                )
            )
            row["execution_note"] = f"measurement_fix:{r.notes}"
            row["measurement_fix_artifact_dir"] = r.artifact_dir
            row["measurement_fix_updated_utc"] = r.updated_utc
        queue_out.append(row)

    # Write outputs.
    write_csv(Path(args.tickets_out), tickets_out)
    write_csv(Path(args.queue_out), queue_out)

    results_csv_rows = [
        {
            "fix_ticket_id": r.fix_ticket_id,
            "claim_id": r.claim_id,
            "status": r.status,
            "metric_match_out": r.metric_match_out,
            "checks_passed": str(r.checks_passed),
            "checks_failed": str(r.checks_failed),
            "notes": r.notes,
            "artifact_dir": r.artifact_dir,
            "updated_utc": r.updated_utc,
        }
        for r in results
    ]
    write_csv(Path(args.results_csv), results_csv_rows)

    status_counts: Dict[str, int] = {}
    for r in results:
        status_counts[r.status] = status_counts.get(r.status, 0) + 1

    lines: List[str] = []
    lines.append("# Measurement Fix Execution Summary")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append(f"Tickets executed: {len(results)}")
    lines.append("")
    lines.append("## Status Counts")
    for k in sorted(status_counts.keys()):
        lines.append(f"- {k}: {status_counts[k]}")
    lines.append("")
    lines.append("## Ticket Results")
    lines.append("")
    lines.append("| Ticket | Claim | Status | Metric Match Out | Checks (pass/fail) | Notes |")
    lines.append("|---|---|---|---|---|---|")
    for r in results:
        lines.append(
            f"| {r.fix_ticket_id} | {r.claim_id} | {r.status} | {r.metric_match_out} | {r.checks_passed}/{r.checks_failed} | {r.notes} |"
        )

    md_path = Path(args.results_md)
    md_path.parent.mkdir(parents=True, exist_ok=True)
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"wrote_results_csv={args.results_csv} rows={len(results)}")
    print(f"wrote_results_md={args.results_md}")
    print(f"wrote_tickets_out={args.tickets_out}")
    print(f"wrote_queue_out={args.queue_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
