#!/usr/bin/env python3
"""Generate markdown claim dossiers from ranking + reproducibility artifacts."""

from __future__ import annotations

import argparse
import csv
import json
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Generate claim dossiers")
    p.add_argument("--ranking", required=True, help="Path to ranking CSV")
    p.add_argument("--claims", required=True, help="Path to claims CSV")
    p.add_argument("--queue", required=True, help="Path to promotion queue CSV")
    p.add_argument("--adjudication", required=True, help="Path to adjudication CSV")
    p.add_argument("--measurement-audit", required=True, help="Path to measurement audit CSV")
    p.add_argument("--triage", required=True, help="Path to numeric triage CSV")
    p.add_argument("--repro-root", required=True, help="Root dir for per-claim repro artifacts")
    p.add_argument("--output-dir", required=True, help="Dir for per-claim dossier markdown files")
    p.add_argument("--index-md", required=True, help="Output markdown index")
    p.add_argument("--index-csv", required=True, help="Output CSV index")
    p.add_argument("--recommendation", default="promote_to_claim_dossier", help="Ranking recommendation filter")
    p.add_argument("--limit", type=int, default=0, help="Optional max dossiers; 0 means no limit")
    return p.parse_args()


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def read_rows(path: Path) -> List[Dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def map_by(rows: List[Dict[str, str]], key: str) -> Dict[str, Dict[str, str]]:
    out: Dict[str, Dict[str, str]] = {}
    for r in rows:
        k = (r.get(key) or "").strip()
        if k:
            out[k] = r
    return out


def read_json(path: Path) -> Dict[str, object]:
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}


def to_int(s: str, default: int = 0) -> int:
    try:
        return int(float(s))
    except (TypeError, ValueError):
        return default


def to_float(s: str, default: float = 0.0) -> float:
    try:
        return float(s)
    except (TypeError, ValueError):
        return default


def short(text: str, n: int = 500) -> str:
    text = (text or "").strip().replace("\r", " ").replace("\n", " ")
    if len(text) <= n:
        return text
    return text[: n - 3] + "..."


def action_items(metric_match: str, truncated: bool) -> List[str]:
    items: List[str] = []
    if metric_match == "partial":
        items.append("Apply measurement alignment patch before publication claims.")
    if truncated:
        items.append("Rerun uncapped numeric extraction for full-data confirmation.")
    if not items:
        items.append("Promote to claim dossier review board and attach reproducibility packet.")
    return items


def write_dossier(
    out_path: Path,
    rank_row: Dict[str, str],
    claim: Dict[str, str],
    queue: Dict[str, str],
    adj: Dict[str, str],
    meas: Dict[str, str],
    tri: Dict[str, str],
    input_summary: Dict[str, object],
    verdict: Dict[str, object],
) -> None:
    claim_id = rank_row.get("claim_id", "")
    rank = rank_row.get("rank", "")
    truncated = str(rank_row.get("truncated", "False")) == "True"
    metric_match = rank_row.get("metric_match", "unknown")

    lines: List[str] = []
    lines.append(f"# Claim Dossier: {claim_id}")
    lines.append("")
    lines.append("## Metadata")
    lines.append(f"- rank: {rank}")
    lines.append(f"- review_score: {rank_row.get('review_score','')}")
    lines.append(f"- tier: {rank_row.get('tier','')}")
    lines.append(f"- recommendation: {rank_row.get('recommendation','')}")
    lines.append(f"- priority_note: {rank_row.get('priority_note','')}")
    lines.append(f"- source_file: {claim.get('filename','')}")
    lines.append(f"- source_path: {claim.get('source_path','')}")
    lines.append(f"- generated_utc: {utc_now()}")

    lines.append("")
    lines.append("## Claim Statement")
    lines.append(f"- claim_type: {claim.get('claim_type','')}")
    lines.append(f"- short_statement: {short(claim.get('short_statement',''), 650)}")
    lines.append(f"- assumptions: {short(claim.get('assumptions',''), 300)}")
    lines.append(f"- excerpt: {short(claim.get('source_excerpt',''), 700)}")

    lines.append("")
    lines.append("## Validation Snapshot")
    lines.append(f"- adjudication_decision: {adj.get('decision','')}")
    lines.append(f"- adjudication_score: {adj.get('adjudication_score','')}")
    lines.append(f"- queue_status: {queue.get('queue_status','')}")
    lines.append(f"- ladder_status: {queue.get('ladder_status','')}")
    lines.append(f"- max_rel_float64_vs_mpmath: {rank_row.get('max_rel_float_vs_mpmath','')}")
    lines.append(f"- max_rel_decimal128_vs_mpmath: {rank_row.get('max_rel_decimal_vs_mpmath','')}")
    lines.append(f"- metric_match: {metric_match}")
    lines.append(f"- notation_match: {rank_row.get('notation_match','')}")
    lines.append(f"- float_risk: {rank_row.get('float_risk','')}")

    usable = to_int(str(input_summary.get("usable_values", "0")), 0)
    tokens = to_int(str(input_summary.get("tokens_extracted", "0")), 0)
    extract_meta = input_summary.get("extraction", {}) if isinstance(input_summary.get("extraction", {}), dict) else {}
    th = input_summary.get("thresholds", {}) if isinstance(input_summary.get("thresholds", {}), dict) else {}

    lines.append("")
    lines.append("## Numeric Repro Details")
    lines.append(f"- usable_values: {usable}")
    lines.append(f"- tokens_extracted: {tokens}")
    lines.append(f"- extraction_method: {extract_meta.get('method','')}")
    lines.append(f"- extraction_truncated: {extract_meta.get('truncated','')}")
    lines.append(f"- stable_threshold: {th.get('stable','')}")
    lines.append(f"- sensitive_threshold: {th.get('sensitive','')}")
    lines.append(f"- artifact_dir: {queue.get('artifact_dir','')}")

    lines.append("")
    lines.append("## Measurement + Notation")
    lines.append(f"- measurement_metric_match: {meas.get('metric_match', 'unknown')}")
    lines.append(f"- measurement_notation_match: {meas.get('notation_match', 'unknown')}")
    lines.append(f"- measurement_required_fixes: {meas.get('required_fixes', '')}")
    lines.append(f"- triage_precision_plan: {tri.get('precision_plan', '')}")
    lines.append(f"- triage_numeric_literals_detected: {tri.get('numeric_literals_detected', '')}")

    lines.append("")
    lines.append("## Verdict")
    lines.append(f"- repro_final_status: {verdict.get('final_status', queue.get('ladder_status', ''))}")
    lines.append(f"- dossier_readiness: {'ready' if (metric_match == 'pass' and not truncated) else 'conditional'}")

    lines.append("")
    lines.append("## Required Next Actions")
    for item in action_items(metric_match, truncated):
        lines.append(f"- {item}")

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    ranking_rows = read_rows(Path(args.ranking))
    selected = [r for r in ranking_rows if r.get("recommendation") == args.recommendation]
    selected.sort(key=lambda r: to_int(r.get("rank", "9999"), 9999))
    if args.limit > 0:
        selected = selected[: args.limit]

    claims_map = map_by(read_rows(Path(args.claims)), "claim_id")
    queue_map = map_by(read_rows(Path(args.queue)), "claim_id")
    adj_map = map_by(read_rows(Path(args.adjudication)), "claim_id")
    meas_map = map_by(read_rows(Path(args.measurement_audit)), "claim_id")
    tri_map = map_by(read_rows(Path(args.triage)), "claim_id")

    output_dir = Path(args.output_dir)
    repro_root = Path(args.repro_root)

    index_rows: List[Dict[str, str]] = []
    for rr in selected:
        cid = rr.get("claim_id", "")
        claim = claims_map.get(cid, {})
        queue = queue_map.get(cid, {})
        adj = adj_map.get(cid, {})
        meas = meas_map.get(cid, {})
        tri = tri_map.get(cid, {})

        artifact_dir_str = queue.get("artifact_dir", "")
        artifact_dir = Path(artifact_dir_str) if artifact_dir_str else (repro_root / cid)

        input_summary = read_json(artifact_dir / "input_summary.json")
        verdict = read_json(artifact_dir / "repro_verdict.json")

        rank_num = to_int(rr.get("rank", "0"), 0)
        dossier_name = f"{rank_num:02d}_{cid}.md"
        dossier_path = output_dir / dossier_name
        write_dossier(dossier_path, rr, claim, queue, adj, meas, tri, input_summary, verdict)

        index_rows.append(
            {
                "rank": str(rank_num),
                "claim_id": cid,
                "review_score": rr.get("review_score", ""),
                "tier": rr.get("tier", ""),
                "recommendation": rr.get("recommendation", ""),
                "dossier_path": str(dossier_path),
                "artifact_dir": str(artifact_dir),
            }
        )

    # Write index CSV.
    index_csv = Path(args.index_csv)
    index_csv.parent.mkdir(parents=True, exist_ok=True)
    with index_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(
            f,
            fieldnames=[
                "rank",
                "claim_id",
                "review_score",
                "tier",
                "recommendation",
                "dossier_path",
                "artifact_dir",
            ],
        )
        w.writeheader()
        w.writerows(index_rows)

    # Write index markdown.
    tier_counts = Counter(r["tier"] for r in index_rows)
    lines: List[str] = []
    lines.append("# Claim Dossier Index")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append(f"Recommendation filter: {args.recommendation}")
    lines.append(f"Dossiers generated: {len(index_rows)}")
    lines.append("")
    lines.append("## Tier Counts")
    for k, v in sorted(tier_counts.items()):
        lines.append(f"- {k}: {v}")
    lines.append("")
    lines.append("## Claims")
    lines.append("")
    lines.append("| Rank | Claim | Score | Tier | Dossier |")
    lines.append("|---:|---|---:|---|---|")
    for r in index_rows:
        lines.append(
            f"| {r['rank']} | {r['claim_id']} | {r['review_score']} | {r['tier']} | {r['dossier_path']} |"
        )

    index_md = Path(args.index_md)
    index_md.parent.mkdir(parents=True, exist_ok=True)
    index_md.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"wrote_index_csv={index_csv} rows={len(index_rows)}")
    print(f"wrote_index_md={index_md}")
    print(f"wrote_dossiers_dir={output_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
