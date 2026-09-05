#!/usr/bin/env python3
"""Execute two-model quorum task pack in offline-proxy mode.

This script DOES NOT call external model APIs. It produces structured
proxy vote artifacts using two independent deterministic rubrics so tasks
can proceed with full traceability while awaiting live-model quorum.
"""

from __future__ import annotations

import argparse
import csv
import json
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Sequence


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_float(s: str, default: float = 0.0) -> float:
    try:
        return float(s)
    except Exception:
        return default


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Run two-model quorum pack in offline proxy mode")
    p.add_argument("--task-pack", required=True, help="Quorum task pack CSV")
    p.add_argument("--ranking", required=True, help="Ranking CSV")
    p.add_argument("--queue", required=True, help="Promotion queue CSV")
    p.add_argument("--dossier-index", required=True, help="Dossier index CSV")
    p.add_argument("--output-root", required=True, help="Root reports/quorum output dir")
    p.add_argument("--task-pack-out", required=True, help="Updated task pack CSV")
    p.add_argument("--summary-md", required=True, help="Summary markdown")
    p.add_argument("--summary-csv", required=True, help="Summary CSV")
    return p.parse_args()


def read_csv(path: Path) -> List[Dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def write_csv(path: Path, rows: List[Dict[str, str]], fieldnames: Sequence[str] | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    if fieldnames is None:
        seen: List[str] = []
        for r in rows:
            for k in r.keys():
                if k not in seen:
                    seen.append(k)
        fieldnames = seen
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)


def write_json(path: Path, obj: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2), encoding="utf-8")


def load_map(rows: List[Dict[str, str]], key: str) -> Dict[str, Dict[str, str]]:
    out: Dict[str, Dict[str, str]] = {}
    for r in rows:
        k = (r.get(key) or "").strip()
        if k:
            out[k] = r
    return out


def vote_model_a(review_score: float, ladder: str, metric: str) -> tuple[str, float, List[str]]:
    rationale: List[str] = []
    conf = 0.55
    if ladder == "stable":
        conf += 0.20
        rationale.append("numeric_stability_pass")
    else:
        rationale.append("numeric_stability_not_pass")
    if metric == "pass":
        conf += 0.15
        rationale.append("measurement_integrity_pass")
    else:
        rationale.append("measurement_integrity_not_pass")
    if review_score >= 98:
        conf += 0.10
        status = "approve_promote"
        rationale.append("high_review_score")
    elif review_score >= 92:
        conf += 0.05
        status = "approve_with_caveats"
        rationale.append("moderate_review_score")
    else:
        status = "escalate"
        rationale.append("low_review_score")

    if ladder != "stable" or metric != "pass":
        status = "escalate"
    conf = max(0.0, min(conf, 0.98))
    return status, conf, rationale


def vote_model_b(review_score: float, ladder: str, metric: str) -> tuple[str, float, List[str]]:
    rationale: List[str] = []
    conf = 0.52
    if ladder == "stable":
        conf += 0.22
        rationale.append("numeric_stability_pass")
    else:
        rationale.append("numeric_stability_not_pass")
    if metric == "pass":
        conf += 0.16
        rationale.append("measurement_integrity_pass")
    else:
        rationale.append("measurement_integrity_not_pass")

    if review_score >= 99:
        conf += 0.07
        status = "approve_promote"
        rationale.append("very_high_review_score")
    elif review_score >= 90:
        conf += 0.05
        status = "approve_with_caveats"
        rationale.append("acceptable_review_score")
    else:
        status = "escalate"
        rationale.append("insufficient_review_score")

    if ladder != "stable" or metric != "pass":
        status = "escalate"
    conf = max(0.0, min(conf, 0.98))
    return status, conf, rationale


def merge_decision(vote_a: str, vote_b: str) -> tuple[str, str]:
    if vote_a == vote_b:
        if vote_a == "approve_promote":
            return "consensus_promote", "Both proxy votes approve promotion."
        if vote_a == "approve_with_caveats":
            return "consensus_caveated", "Both proxy votes approve with caveats."
        return "consensus_escalate", "Both proxy votes request escalation."
    return "conflict_escalate", "Proxy votes disagree; escalate to live multi-model adjudication."


def write_merged_md(path: Path, claim_id: str, task_id: str, vote_a: Dict[str, object], vote_b: Dict[str, object], merged_status: str, merged_note: str, dossier_path: str) -> None:
    lines: List[str] = []
    lines.append(f"# Quorum Decision: {claim_id}")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append(f"Task: {task_id}")
    lines.append(f"Mode: offline_proxy")
    lines.append(f"Dossier: {dossier_path}")
    lines.append("")
    lines.append("## Proxy Votes")
    lines.append(f"- Model A: {vote_a['status_class']} (confidence={vote_a['confidence']})")
    lines.append(f"- Model B: {vote_b['status_class']} (confidence={vote_b['confidence']})")
    lines.append("")
    lines.append("## Merged Result")
    lines.append(f"- merged_status: {merged_status}")
    lines.append(f"- note: {merged_note}")
    lines.append("")
    lines.append("## Release-Gate Note")
    lines.append(
        "- This artifact is an offline proxy adjudication. Final publication-gate quorum requires live external model execution per routing matrix."
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()

    tasks = read_csv(Path(args.task_pack))
    ranking = load_map(read_csv(Path(args.ranking)), "claim_id")
    queue = load_map(read_csv(Path(args.queue)), "claim_id")
    dossier_idx = load_map(read_csv(Path(args.dossier_index)), "claim_id")

    out_root = Path(args.output_root)

    result_rows: List[Dict[str, str]] = []
    updated_tasks: List[Dict[str, str]] = []

    for t in tasks:
        status_in = (t.get("status") or "").strip().lower()
        if status_in not in {"queued", "retry", ""}:
            updated_tasks.append(dict(t))
            continue

        claim_id = t.get("claim_id", "")
        task_id = t.get("task_id", "")
        rank_row = ranking.get(claim_id, {})
        qrow = queue.get(claim_id, {})
        drow = dossier_idx.get(claim_id, {})

        review_score = parse_float(rank_row.get("review_score"), 0.0)
        ladder = qrow.get("ladder_status", "")
        metric = qrow.get("metric_match", "")

        vote_a_status, vote_a_conf, vote_a_rationale = vote_model_a(review_score, ladder, metric)
        vote_b_status, vote_b_conf, vote_b_rationale = vote_model_b(review_score, ladder, metric)

        claim_dir = out_root / claim_id
        model_a_path = claim_dir / "model_a_vote.json"
        model_b_path = claim_dir / "model_b_vote.json"
        merged_path = claim_dir / "merged_quorum_decision.md"

        vote_a_obj = {
            "claim_id": claim_id,
            "task_id": task_id,
            "model_lane": t.get("model_a", ""),
            "execution_mode": "offline_proxy_no_api",
            "external_api_called": False,
            "status_class": vote_a_status,
            "confidence": round(vote_a_conf, 3),
            "review_score": review_score,
            "numeric_ladder_status": ladder,
            "metric_match": metric,
            "rationale": vote_a_rationale,
            "generated_utc": utc_now(),
        }
        vote_b_obj = {
            "claim_id": claim_id,
            "task_id": task_id,
            "model_lane": t.get("model_b", ""),
            "execution_mode": "offline_proxy_no_api",
            "external_api_called": False,
            "status_class": vote_b_status,
            "confidence": round(vote_b_conf, 3),
            "review_score": review_score,
            "numeric_ladder_status": ladder,
            "metric_match": metric,
            "rationale": vote_b_rationale,
            "generated_utc": utc_now(),
        }

        merged_status, merged_note = merge_decision(vote_a_status, vote_b_status)

        write_json(model_a_path, vote_a_obj)
        write_json(model_b_path, vote_b_obj)
        write_merged_md(
            merged_path,
            claim_id,
            task_id,
            vote_a_obj,
            vote_b_obj,
            merged_status,
            merged_note,
            drow.get("dossier_path", ""),
        )

        row = dict(t)
        row["status"] = "executed_proxy"
        row["updated_utc"] = utc_now()
        row["execution_mode"] = "offline_proxy_no_api"
        row["external_quorum_complete"] = "no"
        row["merged_status"] = merged_status
        row["execution_notes"] = merged_note
        row["output_artifacts"] = f"{model_a_path}|{model_b_path}|{merged_path}"
        updated_tasks.append(row)

        result_rows.append(
            {
                "task_id": task_id,
                "claim_id": claim_id,
                "status": "executed_proxy",
                "merged_status": merged_status,
                "external_quorum_complete": "no",
                "output_dir": str(claim_dir),
                "updated_utc": utc_now(),
            }
        )

    write_csv(Path(args.task_pack_out), updated_tasks)
    write_csv(
        Path(args.summary_csv),
        result_rows,
        fieldnames=["task_id", "claim_id", "status", "merged_status", "external_quorum_complete", "output_dir", "updated_utc"],
    )

    merged_counts = Counter(r["merged_status"] for r in result_rows)

    lines: List[str] = []
    lines.append("# Two-Model Quorum Pack Execution (Offline Proxy)")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append(f"Tasks executed: {len(result_rows)}")
    lines.append("Execution mode: offline_proxy_no_api")
    lines.append("")
    lines.append("## Merged Status Counts")
    for k, v in sorted(merged_counts.items()):
        lines.append(f"- {k}: {v}")
    lines.append("")
    lines.append("## Task Results")
    lines.append("| Task | Claim | Status | Merged Status | External Quorum Complete |")
    lines.append("|---|---|---|---|---|")
    for r in result_rows:
        lines.append(
            f"| {r['task_id']} | {r['claim_id']} | {r['status']} | {r['merged_status']} | {r['external_quorum_complete']} |"
        )
    lines.append("")
    lines.append("## Release-Gate Note")
    lines.append(
        "- These outputs are structured proxies for orchestration continuity. Execute live provider-based quorum to satisfy strict publication gate requirements."
    )

    md_path = Path(args.summary_md)
    md_path.parent.mkdir(parents=True, exist_ok=True)
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"wrote_task_pack={args.task_pack_out}")
    print(f"wrote_summary_md={args.summary_md}")
    print(f"wrote_summary_csv={args.summary_csv} rows={len(result_rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
