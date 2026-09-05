#!/usr/bin/env python3
"""Generate focused measurement-fix tickets for partial-metric claims."""

from __future__ import annotations

import argparse
import csv
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List


STAT_TERMS = {"p_value", "confidence", "effect_size", "welch", "pearson", "wilson", "significant"}
ERROR_TERMS = {"maxerror", "avgerror", "residue", "detectedresidues", "perfectmatch"}
RUNTIME_TERMS = {"runtime", "elapsed", "speedup", "efficiency"}


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Generate measurement-fix queue for partial metric claims")
    p.add_argument("--ranking", required=True, help="Ranking CSV path")
    p.add_argument("--claims", required=True, help="Claims CSV path")
    p.add_argument("--output-csv", required=True, help="Fix ticket CSV output")
    p.add_argument("--output-md", required=True, help="Fix plan markdown output")
    p.add_argument("--filter-recommendation", default="measurement_fix_then_promote")
    return p.parse_args()


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def read_csv(path: Path) -> List[Dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def map_by(rows: List[Dict[str, str]], key: str) -> Dict[str, Dict[str, str]]:
    out: Dict[str, Dict[str, str]] = {}
    for r in rows:
        k = (r.get(key) or "").strip()
        if k:
            out[k] = r
    return out


def family_for_text(text: str) -> str:
    t = (text or "").lower()
    stat_hits = sum(1 for x in STAT_TERMS if x in t)
    err_hits = sum(1 for x in ERROR_TERMS if x in t)
    run_hits = sum(1 for x in RUNTIME_TERMS if x in t)
    if stat_hits >= max(err_hits, run_hits, 1):
        return "statistical_significance_pack"
    if err_hits >= max(stat_hits, run_hits, 1):
        return "residue_error_pack"
    if run_hits >= max(stat_hits, err_hits, 1):
        return "runtime_efficiency_pack"
    return "general_lrc_metric_pack"


def canonical_definition(family: str) -> str:
    if family == "statistical_significance_pack":
        return "Define primary metric as hypothesis-test object with statistic, p_value, alpha, effect_size, confidence_interval, and sample_size."
    if family == "residue_error_pack":
        return "Define primary metric as residue consistency tuple: max_error, avg_error, perfect_match_rate, and isolation_count over explicit n,phi grid."
    if family == "runtime_efficiency_pack":
        return "Define primary metric as runtime-normalized efficiency: throughput, elapsed_sec, speedup_vs_baseline, and confidence interval over repeated seeds."
    return "Define a single primary metric with explicit units, denominator, and acceptance threshold, plus supporting diagnostics."


def required_columns(family: str) -> str:
    base = ["claim_id", "run_id", "seed", "n", "phi_n", "metric_name", "metric_value", "metric_unit", "acceptance_threshold"]
    if family == "statistical_significance_pack":
        extra = ["statistic", "p_value", "alpha", "effect_size", "confidence_interval", "sample_size"]
    elif family == "residue_error_pack":
        extra = ["max_error", "avg_error", "perfect_match", "detected_residues", "expected_residues", "isolation_count"]
    elif family == "runtime_efficiency_pack":
        extra = ["elapsed_sec", "runtime_ms", "throughput", "speedup_vs_baseline", "replicate_count"]
    else:
        extra = ["notes"]
    return "|".join(base + extra)


def acceptance_test(family: str) -> str:
    if family == "statistical_significance_pack":
        return "Recomputed p_value matches recorded p_value within 1e-12 and decision(alpha) is unchanged in float64/decimal128/mpmath."
    if family == "residue_error_pack":
        return "Recomputed max_error/avg_error differ by <=1e-12 relative and perfect_match classification is invariant across precisions."
    if family == "runtime_efficiency_pack":
        return "Recomputed speedup and throughput vary <=2% across independent reruns with fixed seeds and same hardware profile."
    return "Metric recomputation matches recorded values within declared tolerance and units are consistent end-to-end."


def est_runtime_min(family: str) -> int:
    return {
        "statistical_significance_pack": 35,
        "residue_error_pack": 40,
        "runtime_efficiency_pack": 30,
        "general_lrc_metric_pack": 25,
    }.get(family, 25)


def main() -> int:
    args = parse_args()

    ranking = read_csv(Path(args.ranking))
    claims = map_by(read_csv(Path(args.claims)), "claim_id")

    selected = [r for r in ranking if r.get("recommendation") == args.filter_recommendation]
    selected.sort(key=lambda r: int(float(r.get("rank") or 9999)))

    tickets: List[Dict[str, str]] = []
    for i, r in enumerate(selected, start=1):
        cid = r.get("claim_id", "")
        c = claims.get(cid, {})
        text = " ".join([c.get("short_statement", ""), c.get("source_excerpt", ""), c.get("filename", "")])
        family = family_for_text(text)
        ticket = {
            "fix_ticket_id": f"MFIX-LRC-{i:04d}",
            "claim_id": cid,
            "rank": r.get("rank", ""),
            "source_file": c.get("filename", ""),
            "source_path": c.get("source_path", ""),
            "detected_metric_family": family,
            "current_issue": "metric_match_partial",
            "canonical_metric_name": family,
            "canonical_definition": canonical_definition(family),
            "required_columns": required_columns(family),
            "unit_policy": "Declare explicit SI-compatible unit or dimensionless tag for each metric_value.",
            "acceptance_test": acceptance_test(family),
            "recompute_needed": "yes",
            "estimated_local_runtime_min": str(est_runtime_min(family)),
            "owner": "local_python",
            "status": "queued",
            "created_utc": utc_now(),
        }
        tickets.append(ticket)

    out_csv = Path(args.output_csv)
    out_csv.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "fix_ticket_id",
        "claim_id",
        "rank",
        "source_file",
        "source_path",
        "detected_metric_family",
        "current_issue",
        "canonical_metric_name",
        "canonical_definition",
        "required_columns",
        "unit_policy",
        "acceptance_test",
        "recompute_needed",
        "estimated_local_runtime_min",
        "owner",
        "status",
        "created_utc",
    ]
    with out_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(tickets)

    fam_counts = Counter(t["detected_metric_family"] for t in tickets)
    total_runtime = sum(int(t["estimated_local_runtime_min"]) for t in tickets)

    lines: List[str] = []
    lines.append("# Measurement Fix Pass (Cycle 002)")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append(f"Claims queued: {len(tickets)}")
    lines.append(f"Estimated serial runtime (min): {total_runtime}")
    lines.append("")
    lines.append("## Family Counts")
    for k, v in sorted(fam_counts.items()):
        lines.append(f"- {k}: {v}")
    lines.append("")
    lines.append("## Tickets")
    lines.append("")
    lines.append("| Ticket | Claim | Family | Runtime(min) | Acceptance Test |")
    lines.append("|---|---|---|---:|---|")
    for t in tickets:
        lines.append(
            f"| {t['fix_ticket_id']} | {t['claim_id']} | {t['detected_metric_family']} | {t['estimated_local_runtime_min']} | {t['acceptance_test']} |"
        )

    out_md = Path(args.output_md)
    out_md.parent.mkdir(parents=True, exist_ok=True)
    out_md.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"wrote_csv={out_csv} rows={len(tickets)}")
    print(f"wrote_md={out_md}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
